"""Validate complete, attributed sources of the pinned statement definitions."""
import argparse
import hashlib
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]

def verify_bytes(data, entry):
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise ValueError(f"Definition source mismatch: {entry['file']}")
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if blob != entry["git_blob"]:
        raise ValueError(f"Git blob mismatch: {entry['file']}")

def check(compare=False, self_test=False):
    manifest = json.loads((ROOT / "definition-evidence/manifest.json").read_text())
    for entry in manifest["sources"]:
        path = (ROOT / entry["file"]).resolve()
        if not path.is_relative_to(ROOT):
            raise ValueError("Definition evidence escapes package")
        data = path.read_bytes()
        verify_bytes(data, entry)
        if compare:
            installed = subprocess.check_output(["git", "-C", str(ROOT / ".lake/packages/mathlib"),
                "show", f"{entry['commit']}:{entry['upstream_path']}"])
            if installed != data:
                raise ValueError(f"Installed pinned source differs: {entry['upstream_path']}")
        if self_test:
            try:
                verify_bytes(data + b"\n-- intentional rejection control\n", entry)
            except ValueError:
                pass
            else:
                raise ValueError("Corrupted definition snapshot was accepted")
    print(f"Verified {len(manifest['sources'])} complete pinned definition sources.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--compare-mathlib", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    check(args.compare_mathlib, args.self_test)
