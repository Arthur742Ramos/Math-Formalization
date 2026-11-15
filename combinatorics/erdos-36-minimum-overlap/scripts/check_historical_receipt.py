#!/usr/bin/env python3
"""Check historical source and log bindings; do not claim a fresh Lean run."""

from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
RECEIPT = ROOT / "reviews/full_verification/kernel_verification.json"
EXPECTED_RECEIPT_SHA256 = "a67bbf17b68218b0151e8c164563bc60448e4d225f5344795f29af6f5908955d"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def check_hash(relative: str, expected: str, failures: list[str]) -> None:
    path = ROOT / relative
    if not path.resolve().is_relative_to(ROOT) or not path.is_file():
        failures.append(f"missing or invalid path: {relative}")
    elif digest(path) != expected:
        failures.append(f"hash mismatch: {relative}")


def main() -> None:
    failures: list[str] = []
    if digest(RECEIPT) != EXPECTED_RECEIPT_SHA256:
        raise SystemExit("historical kernel receipt hash mismatch")
    receipt = json.loads(RECEIPT.read_text())
    if receipt.get("status") != "kernel_checked":
        failures.append("historical receipt does not report kernel_checked")
    for path, expected in receipt["proof_sources"].items():
        check_hash(path, expected, failures)

    conventional = json.loads(
        (ROOT / "reviews/full_verification/conventional_surface.json").read_text()
    )
    for filename in ("Challenge.lean", "Solution.lean"):
        build = conventional["builds"][filename]
        if build["exit_code"] != 0:
            failures.append(f"historical conventional build failed: {filename}")
        check_hash(filename, build["source_sha256"], failures)
        check_hash(build["log_path"], build["log_sha256"], failures)

    for filename, item in (
        ("NumericSolution.lean", receipt["builds"]["NumericSolution"]),
        ("AuditNumeric.lean", receipt["axiom_audit_receipt"]),
    ):
        if item["exit_code"] != 0:
            failures.append(f"historical command failed: {filename}")
        check_hash(filename, item["source_sha256"], failures)

    audit_log = ROOT / "reviews/full_verification/AuditNumeric.log"
    check_hash(str(audit_log.relative_to(ROOT)), receipt["axiom_audit_receipt"]["log_sha256"], failures)
    logged = dict(re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit_log.read_text()))
    config = json.loads((ROOT / "comparator.json").read_text())
    selected = set(config["theorem_names"])
    if not selected <= set(receipt["axioms"]) or set(logged) != set(receipt["axioms"]):
        failures.append("selected or logged axiom reports do not match the historical receipt")
    for name, axioms in receipt["axioms"].items():
        if set(axioms) - ALLOWED_AXIOMS or set(logged.get(name, "").replace("\n", " ").replace(" ", "").split(",")) != set(axioms):
            failures.append(f"axiom report mismatch: {name}")

    result = {
        "status": "pass" if not failures else "fail",
        "historical_receipt_sha256": EXPECTED_RECEIPT_SHA256,
        "recorded_proof_and_toolchain_files_checked": len(receipt["proof_sources"]),
        "selected_theorems_checked_in_historical_axiom_log": len(selected),
        "conventional_statement_sources_checked": ["Challenge.lean", "Solution.lean"],
        "scope": "Historical receipt and source-hash consistency only; no Lean build or protected verification was run.",
        "failures": failures,
    }
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
