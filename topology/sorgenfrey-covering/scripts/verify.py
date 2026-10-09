"""Validate the independent nested package and optionally run its Lean checks."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
from check_definitions import check

sys.stdout.reconfigure(encoding="utf-8")

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
TOOLCHAIN = "leanprover/lean4:v4.28.0"

def check_package():
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError("Lean toolchain differs from verified pin")
    if f'rev = "{PIN}"' not in (ROOT / "lakefile.toml").read_text():
        raise ValueError("Lake configuration differs from verified pin")
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    mathlib = [p for p in lock["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != PIN:
        raise ValueError("Mathlib lock differs from verified pin")
    for item in json.loads((ROOT / "reuse.json").read_text()):
        if hashlib.sha256((ROOT / item["path"]).read_bytes()).hexdigest() != item["retained_source_sha256"]:
            raise ValueError(f"Retained source changed: {item['path']}")
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    imports = re.findall(r"^import\s+(\S+)", challenge, re.MULTILINE)
    if imports != ["Counterexamples.SorgenfreyLine", "Mathlib.Topology.Compactness.Lindelof"]:
        raise ValueError("Challenge must import only the pinned upstream definitions")
    for path in [*ROOT.glob("*.lean"), ROOT / "scripts/CompareTypes.lean"]:
        if re.search(r"\b(sorry|admit|axiom)\b", path.read_text(encoding="utf-8")):
            raise ValueError(f"Unfinished or axiom-bearing source: {path.name}")
    config = json.loads((ROOT / "comparator.json").read_text())
    if len(config["theorem_names"]) != 7 or len(config["expected_propositions"]) != 7:
        raise ValueError("Expected seven independent statement contracts")
    metadata = json.loads((ROOT / "formalization.yaml").read_text())
    if metadata["registry_submission"] != "not-submitted":
        raise ValueError("No registry submission is authorized")
    check(self_test=True)
    print("Package layout, retained proof bytes, pins, and independent contracts passed.")

def run_checks(output):
    evidence = ROOT / ".lake/verification"
    evidence.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="2")
    stages = []
    commands = [
        ("build", ["lake", "build"]),
        ("axioms", ["lake", "env", "lean", "AxiomAudit.lean"]),
        ("axiom-whitelist", [sys.executable, "scripts/check_axioms.py", str(evidence / "axioms.log")]),
        ("statements", ["lake", "env", "lean", "scripts/CompareTypes.lean"]),
        ("definitions", [sys.executable, "scripts/check_definitions.py", "--compare-mathlib", "--self-test"]),
        ("kernel", ["lake", "env", "leanchecker", "SorgenfreyCovering", "AxiomAudit", "Challenge", "Solution"]),
    ]
    for name, command in commands:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=1200)
        (evidence / f"{name}.log").write_bytes(result.stdout)
        sys.stdout.write(result.stdout.decode("utf-8", errors="replace"))
        stages.append({"name": name, "exit_code": result.returncode})
        if result.returncode:
            raise SystemExit(result.returncode)
    record = {"status": "pass", "lean_toolchain": TOOLCHAIN, "mathlib_commit": PIN,
              "stages": stages, "scope": "Owned nested package build, independent proposition checks, axiom whitelist and bundled kernel recheck."}
    target = ROOT / output
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(record, indent=2) + "\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-package-only", action="store_true")
    parser.add_argument("--lake-build", action="store_true")
    parser.add_argument("--output", default=".lake/verification.json")
    args = parser.parse_args()
    check_package()
    if args.lake_build:
        run_checks(args.output)
