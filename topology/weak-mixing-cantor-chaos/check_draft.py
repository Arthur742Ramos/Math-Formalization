"""Compatibility entrypoint for the bounded check of this package's sources."""
from pathlib import Path
import subprocess
import sys

script = Path(__file__).resolve().parent / "check_copied_sources.py"
sys.exit(subprocess.run([sys.executable, str(script)], check=False).returncode)
