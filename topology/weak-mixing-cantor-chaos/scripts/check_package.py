"""Check package structure and pinned metadata, not mathematical verification."""
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

if not __debug__:
    raise RuntimeError("Package checks require assertions enabled")
p = Path(__file__).resolve().parents[1]
c = json.loads((p / "comparator.json").read_text(encoding="utf-8"))
m = json.loads((p / "formalization.yaml").read_text(encoding="utf-8"))
theorems = ["CantorChaos.cantor_dense_pair_orbits", "CantorChaos.cantor_uniform_scrambled"]
roles = ["Arthur Freitas Ramos", "David Barros Hulak", "Ruy Jose Guerra Barretto de Queiroz"]
assert c["challenge_module"] == "ChaosChallenge" and c["solution_module"] == "ChaosSolution"
assert c["theorem_names"] == theorems and c["definition_names"] == []
assert set(c["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}
assert m["project"]["authors"] == roles and m["project"]["responsible_maintainers"] == roles
assert m["project"]["license"] == "Apache-2.0"
assert (p / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc2"
lock = json.loads((p / "lake-manifest.json").read_text(encoding="utf-8"))
assert lock["name"] == "cantorChaos"
assert next(x for x in lock["packages"] if x["name"] == "mathlib")["rev"] == "065356127b1dc0016f66b7283ce0ce2c4055aa55"
lake = tomllib.loads((p / "lakefile.toml").read_text(encoding="utf-8"))
assert {"CantorChaos", "ChaosChallenge", "ChaosSolution", "SemanticChallenge",
        "SemanticSolution", "AxiomAudit", "Mycielski"} <= set(lake["defaultTargets"])
challenge = (p / "ChaosChallenge.lean").read_bytes()
subprocess.run([sys.executable, str(p / "scripts/build_challenge.py"), "--check"], check=True)
assert (p / "ChaosSolution.lean").read_text(encoding="utf-8").startswith("module\npublic import CantorChaos\n")
semantic_c = (p / "SemanticChallenge.lean").read_text(encoding="utf-8")
semantic_s = (p / "SemanticSolution.lean").read_text(encoding="utf-8")
assert semantic_c.replace("public import ChaosChallenge", "public import ChaosSolution", 1) == semantic_s
for theorem in theorems:
    assert re.search(r"\btheorem\s+" + re.escape(theorem.split(".")[-1]) + r"\b", challenge.decode("utf-8"))
for source in p.rglob("*.lean"):
    if ".lake" in source.parts:
        continue
    text = source.read_text(encoding="utf-8")
    assert re.search(r"(?m)^module\s*$", text), source
    assert not re.search(r"(?m)\b(sorry|admit)\b|^\s*axiom\s+", text), source
assert len(challenge.splitlines()) <= 1000 and len(challenge) <= 102400
checker = p.parent.parent / "scripts/check_imported_definitions.py"
subprocess.run([sys.executable, str(checker), "--project-path", str(p)], check=True)
print("Package consistency passed; mathematical, canonical and release verification remain separate.")
