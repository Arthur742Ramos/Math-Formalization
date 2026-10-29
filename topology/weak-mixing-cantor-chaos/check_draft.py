import fcntl
import os
import subprocess
import sys

workloads = "/home/formalization/workloads"
stats = os.statvfs(workloads)
available = stats.f_bavail * stats.f_frsize
print(f"linux_available_bytes={available}", flush=True)
if available < 30198988800:
    print("Normal 28 GiB reserve plus startup margin is unavailable.", flush=True)
    sys.exit(2)
lock_path = workloads + "/.heavy-verification.lock"
with open(lock_path, "r") as lock:
    try:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("Shared heavy verification lock is busy.", flush=True)
        sys.exit(3)
    cmd = [
        "python3",
        workloads + "/validation-policy/.git/local-setup/scheduling/parallel_workloads.py",
        "pr43", "--class", "native", "--memory-gib", "6", "--seconds", "240",
        "--cwd", workloads + "/pr43/mycielski-source/topology/mycielski-cantor-independent",
        "--", "/home/formalization/.elan/bin/lake", "env", "lean", "-j1", "-M4096",
        "/mnt/q/Codex/2026-10-29/topology-chaos/topology/weak-mixing-cantor-chaos/CantorChaos.lean",
    ]
    sys.exit(subprocess.run(cmd, check=False).returncode)
