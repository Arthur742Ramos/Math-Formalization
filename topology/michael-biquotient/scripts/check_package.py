"""Check the nested package's pins, transparent Challenge, and axiom report."""
import argparse
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def check_roles(project, readme):
    """Check each declared project role independently against its README block."""
    assert "Authorship and maintenance remain with" not in readme, \
        "Stale combined authorship/maintenance claim in README"
    for field, label in (("authors", "Project authors"),
                         ("responsible_maintainers", "Responsible maintainers")):
        names = project[field]
        assert names and all(isinstance(name, str) and name.strip() for name in names), label
        assert len(names) == len(set(names)), f"Duplicate {label} in metadata"
        blocks = re.findall(rf"(?m)^{re.escape(label)}:\s*\n((?:- [^\n]+\n?)+)", readme)
        assert len(blocks) == 1, f"Expected one {label} block in README"
        declared = [line[2:].strip() for line in blocks[0].splitlines()]
        assert declared == names, f"{label} in README differ from project.{field}"

def check(axiom_log=None):
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc2"
    assert f'rev = "{PIN}"' in (ROOT / "lakefile.toml").read_text()
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    assert next(p for p in lock["packages"] if p["name"] == "mathlib")["rev"] == PIN
    config = json.loads((ROOT / "comparator.json").read_text())
    assert set(config["permitted_axioms"]) == AXIOMS
    assert len(config["theorem_names"]) == 7
    assert (ROOT / "Challenge.lean").read_bytes() == (ROOT / "MichaelBiquotient.lean").read_bytes()
    for path in ROOT.rglob("*.lean"):
        if ".lake" in path.relative_to(ROOT).parts:
            continue
        source = path.read_text(encoding="utf-8")
        assert re.search(r"^module\s*$", source, re.MULTILINE), str(path)
        assert not re.search(r"\b(sorry|admit|axiom)\b", source), str(path)
        assert len(source.splitlines()) <= (1000 if path.name == "Challenge.lean" else 10000)
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    assert len(challenge.encode()) <= 100 * 1024
    imports = re.findall(r"^public import (\S+)$", challenge, re.MULTILINE)
    assert imports and all(name.startswith("Mathlib.") for name in imports)
    metadata = json.loads((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    check_roles(metadata["project"], (ROOT / "README.md").read_text(encoding="utf-8"))
    assert metadata["registry_submission"] == "not-submitted"
    if axiom_log:
        source = pathlib.Path(axiom_log).read_text(encoding="utf-8")
        reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", source))
        for name in config["theorem_names"]:
            assert name in reports, f"Missing axiom report: {name}"
            actual = {x.strip() for x in reports[name].split(",") if x.strip()}
            assert actual <= AXIOMS, f"Unpermitted axioms for {name}: {actual - AXIOMS}"
    print(json.dumps({"package_checks": "pass", "challenge_lines": len(challenge.splitlines()),
                      "proof_sha256": hashlib.sha256((ROOT / "MichaelBiquotient.lean").read_bytes()).hexdigest(),
                      "theorem_names": config["theorem_names"]}, indent=2))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--axiom-log")
    check(parser.parse_args().axiom_log)
