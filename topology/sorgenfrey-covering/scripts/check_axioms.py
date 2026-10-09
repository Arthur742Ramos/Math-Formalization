"""Fail if the audit is incomplete or uses foundations outside the stated set."""
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
audits = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text)
if len(audits) != 12:
    raise SystemExit(f"Expected 12 axiom reports, found {len(audits)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for report in audits:
    found = {name.strip() for name in report.split(",") if name.strip()}
    if found - allowed:
        raise SystemExit(f"Unexpected axioms: {sorted(found - allowed)}")
if "sorryAx" in text:
    raise SystemExit("Audit contains sorryAx")
print("All 12 declarations use only propext, Classical.choice, and Quot.sound.")
