"""Check the statement surface, exact pins, roles and selected axiom closures."""
import argparse
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TEAM = ["Arthur Freitas Ramos", "David Barros Hulak", "Ruy Jose Guerra Barretto de Queiroz"]

def check(axiom_log=None, write_hashes=False):
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc2"
    assert f'rev = "{PIN}"' in (ROOT / "lakefile.toml").read_text()
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    assert lock["name"] == "perfectParacompact"
    assert next(p for p in lock["packages"] if p["name"] == "mathlib")["rev"] == PIN
    config = json.loads((ROOT / "comparator.json").read_text())
    assert set(config["permitted_axioms"]) == AXIOMS
    assert len(config["theorem_names"]) == 6
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    assert challenge == (ROOT / "Transfer.lean").read_text(encoding="utf-8")
    imports = re.findall(r"^public import (\S+)$", challenge, re.MULTILINE)
    assert imports and all(name.startswith("Mathlib.") for name in imports)
    assert len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 300
    sources = {}
    for path in ROOT.glob("*.lean"):
        source = path.read_text(encoding="utf-8-sig")
        assert re.search(r"^module\s*$", source, re.MULTILINE), str(path)
        assert not re.search(r"\b(sorry|admit|axiom)\b", source), str(path)
        assert len(source.splitlines()) <= 10000
        sources[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
    metadata = json.loads((ROOT / "formalization.yaml").read_text())
    readme = (ROOT / "README.md").read_text()
    for field, label in (("authors", "Project authors"), ("responsible_maintainers", "Responsible maintainers")):
        assert metadata["project"][field] == TEAM
        blocks = re.findall(rf"(?m)^{re.escape(label)}:\s*\n((?:- [^\n]+\n?)+)", readme)
        assert len(blocks) == 1
        assert [line[2:].strip() for line in blocks[0].splitlines()] == TEAM
    for name in config["theorem_names"]:
        assert f"theorem {name.rsplit('.', 1)[1]} " in challenge
    if axiom_log:
        reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", pathlib.Path(axiom_log).read_text(encoding="utf-8-sig")))
        for name in config["theorem_names"]:
            assert name in reports, f"Missing declaration axiom report: {name}"
            actual = {x.strip() for x in reports[name].split(",") if x.strip()}
            assert actual <= AXIOMS, (name, actual - AXIOMS)
    for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "comparator.json", "formalization.yaml", "README.md", "AUDIT.md"]:
        sources[name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    if write_hashes:
        (ROOT / "verification").mkdir(exist_ok=True)
        (ROOT / "verification/source-hashes.json").write_text(json.dumps(sources, indent=2) + "\n")
    print(json.dumps({"package_checks": "pass", "challenge_lines": len(challenge.splitlines()),
        "challenge_bytes": len(challenge.encode()), "source_hashes": sources}, indent=2))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--axiom-log")
    parser.add_argument("--write-hashes", action="store_true")
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
