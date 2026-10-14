"""Check source transparency, renderer limits, pins, roles and selected axioms."""
import argparse
import hashlib
import json
import pathlib
import re
from assemble_challenge import assemble

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TEAM = ["Arthur Freitas Ramos", "David Barros Hulak", "Ruy Jose Guerra Barretto de Queiroz"]

def check(axiom_log=None):
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc2"
    assert f'rev = "{PIN}"' in (ROOT / "lakefile.toml").read_text()
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    assert next(p for p in lock["packages"] if p["name"] == "mathlib")["rev"] == PIN
    config = json.loads((ROOT / "comparator.json").read_text())
    assert set(config["permitted_axioms"]) == AXIOMS
    assert len(config["theorem_names"]) == 6
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    assert challenge == assemble(), "Challenge differs from assembled proof modules"
    imports = re.findall(r"^public import (\S+)$", challenge, re.MULTILINE)
    assert imports and all(name.startswith("Mathlib.") for name in imports)
    assert len(challenge.encode()) <= 100 * 1024
    for path in ROOT.glob("*.lean"):
        source = path.read_text(encoding="utf-8-sig")
        assert re.search(r"^module\s*$", source, re.MULTILINE), str(path)
        assert not re.search(r"\b(sorry|admit|axiom)\b", source), str(path)
        assert len(source.splitlines()) < (1001 if path.name == "Challenge.lean" else 10000)
    metadata = json.loads((ROOT / "formalization.yaml").read_text())
    readme = (ROOT / "README.md").read_text()
    for field, label in (("authors", "Project authors"), ("responsible_maintainers", "Responsible maintainers")):
        assert metadata["project"][field] == TEAM
        blocks = re.findall(rf"(?m)^{re.escape(label)}:\s*\n((?:- [^\n]+\n?)+)", readme)
        assert len(blocks) == 1
        assert [line[2:].strip() for line in blocks[0].splitlines()] == TEAM
    assert metadata["registry_submission"] == "not-submitted"
    if axiom_log:
        reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", pathlib.Path(axiom_log).read_text(encoding="utf-8-sig")))
        for name in config["theorem_names"]:
            assert name in reports, f"Missing axiom report: {name}"
            actual = {x.strip() for x in reports[name].split(",") if x.strip()}
            assert actual <= AXIOMS, f"Unpermitted axioms for {name}: {actual - AXIOMS}"
    print(json.dumps({"package_checks":"pass", "challenge_lines":len(challenge.splitlines()),
        "challenge_bytes":len(challenge.encode()), "challenge_sha256":hashlib.sha256(challenge.encode()).hexdigest(),
        "theorem_names":config["theorem_names"]}, indent=2))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--axiom-log")
    check(parser.parse_args().axiom_log)
