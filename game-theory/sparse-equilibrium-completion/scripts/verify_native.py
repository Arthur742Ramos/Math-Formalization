#!/usr/bin/env python3
"""Exact-source native checks using pinned Lean APIs. No canonical sandbox claim."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Verification refuses assertion-disabled Python optimization modes')

assert sys.version_info >= (3, 11), 'Python 3.11+ is required for the repository definition checker'

parser = argparse.ArgumentParser()
parser.add_argument('--out', required=True, type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
repo = root.parents[1]
out = args.out.resolve()
assert not out.is_relative_to(root), 'Evidence belongs outside frozen package'
out.mkdir(parents=True, exist_ok=False)
cfg = json.loads((root / 'comparator.json').read_text())
env = os.environ.copy()
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
assert (root/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
compiler_version = subprocess.check_output([str(prefix/'bin/lean'), '--version'], text=True).strip()
assert '4.35.0-rc2' in compiler_version and '11acb17ec6b07a8f9e9173e6845197929540936b' in compiler_version
env.update(PATH=str(prefix / 'bin') + ':/usr/bin:/bin:/opt/homebrew/bin', LEAN_NUM_THREADS='2')
commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
status = subprocess.check_output(['git', 'status', '--porcelain', '--', str(root)], cwd=repo, text=True)
assert not status, 'Commit the complete package before exact-source verification'
checksource = prefix / 'src/lean/lake/Lake/CLI/Check.lean'
primitive = re.findall(r'^    ``([\w.]+),?$', checksource.read_text().split('def primitiveTargets', 1)[1].split('def builtinTargets', 1)[0], re.M)
assert len(primitive) == 26
deps = sorted((root / '.lake/packages').iterdir())
dependency_paths = [str(prefix / 'lib/lean')] + [str(d / '.lake/build/lib/lean') for d in deps]
mathlib = root / '.lake/packages/mathlib'
dependency_receipts = []
for dep in json.loads((root/'lake-manifest.json').read_text())['packages']:
    path = root/'.lake/packages'/dep['name']
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
    dirty = subprocess.check_output(['git', 'status', '--porcelain'], cwd=path, text=True)
    assert actual == dep['rev'] and not dirty, 'Dependency pin/worktree mismatch: '+dep['name']
    dependency_receipts.append({'name': dep['name'], 'commit': actual, 'clean': True})
targets = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] + cfg['theorem_names'] + cfg['permitted_axioms'] + primitive
files = subprocess.check_output(['git', 'ls-files', '--', str(root)], cwd=repo, text=True).splitlines()
hashes = {f: hashlib.sha256((repo/f).read_bytes()).hexdigest() for f in files}
receipt = {'scope': 'Native macOS exact-source builds, separate protected alias, pinned comparison/axiom APIs, native kernel checks. Not canonical Linux sandbox or registry clearance.',
    'commit': commit, 'package_tree': subprocess.check_output(['git', 'rev-parse', 'HEAD:game-theory/sparse-equilibrium-completion'], cwd=repo, text=True).strip(),
    'source_sha256': hashes, 'config': cfg, 'primitive_targets': primitive, 'checks': [],
    'compiler_version': compiler_version, 'compiler_sha256': hashlib.sha256((prefix/'bin/lean').read_bytes()).hexdigest(),
    'dependency_receipts': dependency_receipts}

def run(name, argv, cwd=root, runenv=env, output=None):
    start = time.monotonic()
    with (out / (name + '.log')).open('w') as log:
        if output is not None:
            with output.open('w') as f:
                result = subprocess.run(argv, cwd=cwd, env=runenv, stdout=f, stderr=log)
        else:
            result = subprocess.run(argv, cwd=cwd, env=runenv, stdout=log, stderr=subprocess.STDOUT)
    receipt['checks'].append({'name': name, 'argv': list(map(str, argv)), 'exit_code': result.returncode,
        'elapsed_seconds': round(time.monotonic()-start, 3),
        'log_sha256': hashlib.sha256((out/(name+'.log')).read_bytes()).hexdigest()})
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(name, result.returncode, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

run('version', [str(prefix/'bin/lean'), '--version'])
run('python-version', [sys.executable, '--version'])
run('source-consistency', [sys.executable, 'scripts/check_package.py'])
run('imported-definitions', [sys.executable, str(repo/'scripts/check_imported_definitions.py'), '--project-path', 'game-theory/sparse-equilibrium-completion', '--dependency-root', str(mathlib)])
# Rebuild package-owned artifacts; preserve the isolated dependency cache.
shutil.rmtree(root/'.lake/build', ignore_errors=True)
run('build', [str(prefix/'bin/lake'), 'build'])
run('axioms', [str(prefix/'bin/lake'), 'env', 'lean', 'AxiomAudit.lean'])
run('native-kernel', [str(prefix/'bin/lake'), 'env', 'leanchecker', 'SECSolution'])
alias = out/'ProtectedSparseCompletion'
alias.mkdir(exist_ok=True)
shutil.copyfile(root/'SECChallenge.lean', alias/'Challenge.lean')
protected_env = env | {'LEAN_PATH': ':'.join([str(out)]+dependency_paths), 'LEAN_SRC_PATH': ':'.join(map(str,deps))}
run('protected-compile', [str(prefix/'bin/lean'), '-j2', '-M3072', '-DwarningAsError=true', '-o', 'ProtectedSparseCompletion/Challenge.olean', 'ProtectedSparseCompletion/Challenge.lean'], out, protected_env)
ch, sol = out/'challenge.ndjson', out/'solution.ndjson'
run('challenge-export', [str(prefix/'bin/leanexport'), 'ProtectedSparseCompletion.Challenge', '--', *targets], out, protected_env, ch)
run('solution-export', [str(prefix/'bin/lake'), 'env', 'leanexport', 'SECSolution', '--', *targets], root, env, sol)
run('pinned-comparator-and-negative-control', [str(prefix/'bin/lean'), '-j2', '-M3072', '--run', str(root/'scripts/CompareExports.lean'), str(ch), str(sol), *cfg['theorem_names']])
run('export-native-kernel', [str(prefix/'bin/leanchecker'), '--silent', '--from-export', str(sol)])
for path in [ch, sol]:
    receipt.setdefault('exports', {})[path.name] = {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}
assert hashes == {f:hashlib.sha256((repo/f).read_bytes()).hexdigest() for f in files}
assert not subprocess.check_output(['git', 'status', '--porcelain', '--', str(root)], cwd=repo, text=True)
receipt['result']='pass'
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
