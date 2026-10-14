"""Assemble the transparent, canonical-Mathlib-only Challenge from the proof modules."""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
MODULES = ["Defs", "Covers", "Sequences", "Thresholds", "Insertion",
           "InsertionReverse", "Product", "ProductReverse", "DowkerCharacterization"]

def assemble():
    imports = set()
    bodies = []
    header = None
    for module in MODULES:
        text = (ROOT / (module + ".lean")).read_text(encoding="utf-8-sig")
        prefix, body = text.split("\nmodule\n", 1)
        if header is None:
            header = prefix
        for name in re.findall(r"^public import (\S+)$", body, re.MULTILINE):
            if name.startswith("Mathlib."):
                imports.add(name)
            else:
                assert name in MODULES
        body = re.sub(r"^public import \S+\n", "", body, flags=re.MULTILINE)
        bodies.append(body.strip())
    return header + "\nmodule\n\n" + "\n".join("public import " + name for name in sorted(imports)) + "\n\n" + "\n\n".join(bodies) + "\n"

if __name__ == "__main__":
    (ROOT / "Challenge.lean").write_text(assemble(), encoding="utf-8", newline="\n")
