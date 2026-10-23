#!/usr/bin/env python3
"""Build default targets and recursive local imports, one Lake job at a time."""
import os
from pathlib import Path
import subprocess
import sys
import tomllib
from protected_sources import checked_graph, discover_sources, require, validate

if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('Serial build refuses optimized Python')


def build_plan(root):
    config = tomllib.loads((root/'lakefile.toml').read_text())
    targets = config['defaultTargets']
    require(len(targets) == len(set(targets)), 'Duplicate default targets')
    files = discover_sources(root)
    require(set(targets) <= files.keys(), 'Every default target must name a local module')
    # Visit only target closure, preserving configured target and import order.
    from protected_sources import import_names
    selected = {}
    def include(name):
        if name in selected:
            return
        selected[name] = files[name].read_bytes()
        for dep in import_names(selected[name]):
            if dep in files:
                include(dep)
    for name in targets:
        include(name)
    order = checked_graph(selected)
    require(set(targets) <= set(order), 'Incomplete target closure')
    return order


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    validate(root)
    require(os.environ.get('LEAN_NUM_THREADS') == '1', 'Use recorded serial profile')
    order = build_plan(root)
    for index, name in enumerate(order, 1):
        print(f'serial-module {index}/{len(order)} {name}', flush=True)
        # Explicit module syntax also covers nested ProtectedSources modules.
        subprocess.run(['lake', 'build', '+'+name+':leanArts'], cwd=root, check=True)
    subprocess.run(['lake', 'build'], cwd=root, check=True)
