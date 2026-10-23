#!/usr/bin/env python3
"""Build every default local target in import order, one Lake invocation at a time."""
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Serial build refuses assertion-disabled Python optimization modes')

root = Path(__file__).resolve().parents[1]
config = tomllib.loads((root/'lakefile.toml').read_text())
targets = config['defaultTargets']
assert len(targets) == len(set(targets)), 'Duplicate default targets'
files = {p.stem: p for p in root.glob('*.lean')}
assert set(targets) <= files.keys(), 'Every default target must name a local module'
visited, active, order = set(), set(), []

def visit(name):
    if name in visited:
        return
    assert name not in active, 'Cyclic local module imports: '+name
    active.add(name)
    text = files[name].read_text()
    # Imports are header commands. Strip comments first so commented examples
    # never become build edges. Nested block comments are handled explicitly.
    clean, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith('/-', pos):
            depth += 1; pos += 2
        elif depth and text.startswith('-/', pos):
            depth -= 1; pos += 2
        elif depth:
            clean.append('\n' if text[pos] == '\n' else ' '); pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        else:
            clean.append(text[pos]); pos += 1
    assert depth == 0, 'Unclosed comment: '+name
    for line in ''.join(clean).splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*', line)
        if re.match(r'\s*(?:(?:public|meta|private)\s+)*import\b', line):
            assert match, 'Unsupported import header in '+name+': '+line
            assert all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', dep) for dep in match[1].split()), 'Unsupported import name in '+name
        if match:
            for dep in match[1].split():
                if dep in files:
                    visit(dep)
    active.remove(name); visited.add(name); order.append(name)

for name in targets:
    visit(name)
assert set(targets) <= visited
assert os.environ.get('LEAN_NUM_THREADS') == '1', 'Use the recorded serial execution profile'
for index, name in enumerate(order, 1):
    print(f'serial-target {index}/{len(order)} {name}', flush=True)
    subprocess.run(['lake', 'build', name], cwd=root, check=True)
# Lake itself checks all configured default targets after the serial traversal.
subprocess.run(['lake', 'build'], cwd=root, check=True)
