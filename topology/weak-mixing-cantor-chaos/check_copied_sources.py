import fcntl
import os
from pathlib import Path
import subprocess
import sys
import uuid

workloads = Path("/home/formalization/workloads")
package = Path(__file__).resolve().parent
retained = workloads / "pr43/mycielski-source/topology/mycielski-cantor-independent"
scheduler = workloads / "validation-policy/.git/local-setup/scheduling/parallel_workloads.py"
if "--inside" in sys.argv:
    build = package / ".lake/build" / ("source-check-" + uuid.uuid4().hex) / "lean"
    (build / "Mycielski").mkdir(parents=True, exist_ok=False)
    inherited = subprocess.check_output(
        ["/home/formalization/.elan/bin/lake", "env", "printenv", "LEAN_PATH"],
        cwd=retained, text=True).strip().split(":")
    # Exclude the old package outputs so imports resolve to newly built Q files.
    old_build = str(retained / ".lake/build/lib/lean")
    search = [str(build)] + [item for item in inherited if item != old_build]
    env = dict(os.environ, LEAN_PATH=":".join(search))
    lean = "/home/formalization/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean"
    for module in ["Mycielski/FusionStep", "Mycielski/Scheme",
                   "Mycielski/Independent", "Mycielski", "CantorChaos",
                   "ChaosChallenge", "ChaosSolution", "SemanticChallenge",
                   "SemanticSolution", "AxiomAudit"]:
        print(f"compiling {module}", flush=True)
        result = subprocess.run(
            [lean, "-j1", "-M4096", "-DwarningAsError=true",
             "-o", str(build / (module + ".olean")), module + ".lean"],
            cwd=package, env=env, check=False)
        if result.returncode:
            sys.exit(result.returncode)
    print("Copied fusion sources and all package entrypoints elaborated with Q-based outputs.", flush=True)
    sys.exit(0)
stats = os.statvfs(workloads)
available = stats.f_bavail * stats.f_frsize
print(f"linux_available_bytes={available}", flush=True)
if available < 30198988800:
    print("Normal 28 GiB reserve plus startup margin is unavailable.", flush=True)
    sys.exit(2)
with open(workloads / ".heavy-verification.lock", "r") as lock:
    try:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("Shared heavy verification lock is busy.", flush=True)
        sys.exit(3)
    cmd = [
        "python3", str(scheduler), "pr43", "--class", "native",
        "--memory-gib", "6", "--seconds", "1200", "--cwd", str(package),
        "--", "python3", str(package / "check_copied_sources.py"), "--inside",
    ]
    sys.exit(subprocess.run(cmd, check=False).returncode)

