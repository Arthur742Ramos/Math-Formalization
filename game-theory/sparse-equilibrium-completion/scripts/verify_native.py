#!/usr/bin/env python3
"""Exact-source native checks using pinned Lean APIs. No canonical sandbox claim."""
import argparse
import atexit
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from check_axiom_reports import check_reports
from protected_sources import validate as validate_protected, FACETS, require_clean_output_tree
from verification_inputs import capture as capture_inputs, file_record

if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('Verification refuses assertion-disabled Python optimization modes')

assert sys.version_info >= (3, 11), 'Python 3.11+ is required for the repository definition checker'

parser = argparse.ArgumentParser()
parser.add_argument('--out', required=True, type=Path)
parser.add_argument('--min-free-bytes', required=True, type=int,
    help='Parent-reviewed free-disk budget before builds/exports; no guessed automatic cache cleanup')
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
repo = root.parents[1]
out = args.out.resolve()
assert not out.is_relative_to(root), 'Evidence belongs outside frozen package'
assert args.min_free_bytes > 0, 'Explicit positive disk budget required'
out.mkdir(parents=True, exist_ok=False)
disk_before = shutil.disk_usage(out)
assert disk_before.free >= args.min_free_bytes, 'Insufficient free disk for reviewed budget'
cfg = json.loads((root / 'comparator.json').read_text())
env = {key: os.environ[key] for key in ["HOME", "TMPDIR", "TMP", "TEMP", "LANG", "LC_ALL"] if key in os.environ}
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
assert (root/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
compiler_version = subprocess.check_output([str(prefix/'bin/lean'), '--version'], text=True).strip()
assert '4.35.0-rc2' in compiler_version and '11acb17ec6b07a8f9e9173e6845197929540936b' in compiler_version
env.update(PATH=':'.join([str(prefix / 'bin'), str(Path(sys.executable).parent), '/usr/local/bin', '/usr/bin', '/bin']), LEAN_NUM_THREADS='1')
lean_flags = ['-j1', '-M8192', '-DwarningAsError=true']
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
tool_paths = ['scripts/check_imported_definitions.py', 'scripts/test_imported_definition_identifiers.py']
for name in tool_paths:
    committed = subprocess.check_output(['git', 'show', commit+':'+name], cwd=repo)
    assert (repo/name).read_bytes() == committed, 'Root verification tool differs from recorded commit: '+name
assert not subprocess.check_output(['git', 'status', '--porcelain', '--', *tool_paths], cwd=repo, text=True)
tool_hashes = {name: hashlib.sha256((repo/name).read_bytes()).hexdigest() for name in tool_paths}
files = subprocess.check_output(['git', 'ls-files', '--', str(root)], cwd=repo, text=True).splitlines()
hashes = {f: hashlib.sha256((repo/f).read_bytes()).hexdigest() for f in files}
protected_map = validate_protected(root)
receipt = {'scope': f'Native {platform.system()} exact-source builds, isolated protected modular source graph, pinned comparison/axiom APIs, native kernel checks. Not a canonical sandbox, renderer, registry or journal clearance.',
    'platform': platform.platform(), 'execution_profile': {'lean_flags': lean_flags, 'LEAN_NUM_THREADS': '1', 'inherited_tool_search_paths': False, 'package_build_scheduling': 'serial recursive local import order, then aggregate Lake default-target check', 'native_export_memory': 'Lean -M does not cap leanexport/leanchecker; parent must schedule external native resource guard independently'},
    'commit': commit, 'package_tree': subprocess.check_output(['git', 'rev-parse', 'HEAD:game-theory/sparse-equilibrium-completion'], cwd=repo, text=True).strip(),
    'source_sha256': hashes, 'config': cfg, 'primitive_targets': primitive, 'checks': [],
    'disk_budget': {'minimum_free_bytes': args.min_free_bytes, 'observed_free_before': disk_before.free, 'not_a_guarantee_of_peak_storage': True},
    'compiler_version': compiler_version, 'compiler_sha256': hashlib.sha256((prefix/'bin/lean').read_bytes()).hexdigest(),
    'dependency_receipts': dependency_receipts, 'verification_tools_sha256': tool_hashes,
    'native_tools_sha256': {name: hashlib.sha256((prefix/'bin'/name).read_bytes()).hexdigest() for name in ['lean', 'lake', 'leanexport', 'leanchecker']}}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

def persist_incomplete_receipt():
    if receipt.get('result') == 'pass':
        return
    receipt['result'] = 'failed'
    receipt['limits_on_failure'] = 'Partial outputs and logs are retained; no incomplete stage is certified.'
    try:
        receipt['partial_exports'] = [file_record(path) for path in [out/'challenge.ndjson', out/'solution.ndjson'] if path.is_file()]
        protected = out/'protected'
        receipt['partial_protected_artifacts'] = [file_record(path) for path in sorted(protected.rglob('*'))
            if path.is_file() and path.name.endswith(FACETS)] if protected.exists() else []
        receipt['partial_package_artifacts'] = [file_record(path) for path in sorted((root/'.lake/build').rglob('*'))
            if path.is_file() and path.name.endswith(FACETS)] if (root/'.lake/build').exists() else []
    except Exception as error:
        receipt['partial_evidence_hash_error'] = str(error)
    (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')

atexit.register(persist_incomplete_receipt)
previous_excepthook = sys.excepthook

def report_exception(kind, value, traceback):
    receipt['exception'] = {'kind': kind.__name__, 'message': str(value)}
    persist_incomplete_receipt()
    previous_excepthook(kind, value, traceback)

sys.excepthook = report_exception

def run(name, argv, cwd=root, runenv=env, output=None):
    start = time.monotonic()
    with (out / (name + '.log')).open('w') as log:
        if output is not None:
            with output.open('w') as f:
                result = subprocess.run(argv, cwd=cwd, env=runenv, stdout=f, stderr=log)
        else:
            result = subprocess.run(argv, cwd=cwd, env=runenv, stdout=log, stderr=subprocess.STDOUT)
    receipt['checks'].append({'name': name, 'argv': list(map(str, argv)), 'exit_code': result.returncode,
        'elapsed_seconds': round(time.monotonic()-start, 3), 'cwd': str(cwd),
        'lean_environment': {key: runenv[key] for key in ['LEAN_NUM_THREADS', 'LEAN_PATH', 'LEAN_SRC_PATH'] if key in runenv},
        'log_sha256': hashlib.sha256((out/(name+'.log')).read_bytes()).hexdigest()})
    if output is not None:
        receipt['checks'][-1]['output'] = {'path': str(output), 'sha256': hashlib.sha256(output.read_bytes()).hexdigest(), 'bytes': output.stat().st_size}
    if result.returncode:
        receipt['result'] = 'failed'
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(name, result.returncode, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

# Include compiler runtime roots explicitly, not merely imports of theorem targets.
input_source_files = [repo/name for name in files if name.endswith('.lean')]
input_extra_files = [repo/name for name in files if not name.endswith('.lean')]+[repo/name for name in tool_paths]
input_extra_files += [Path(sys.executable)]+[prefix/'bin'/name for name in ['lean', 'lake', 'leanexport', 'leanchecker']]+[checksource]
inputs_before = capture_inputs(root, prefix, input_source_files, input_extra_files)
(out/'inputs-before.json').write_text(json.dumps(inputs_before, indent=2)+'\n')
receipt['inputs_before'] = file_record(out/'inputs-before.json')
receipt['runtime_roots'] = ['Init', 'Lean', 'Lake']
(out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')

run('version', [str(prefix/'bin/lean'), '--version'])
run('python-version', [sys.executable, '--version'])
run('source-consistency', [sys.executable, 'scripts/check_package.py'])
run('imported-definitions', [sys.executable, str(repo/'scripts/check_imported_definitions.py'), '--project-path', 'game-theory/sparse-equilibrium-completion', '--dependency-root', str(mathlib)])
# Rebuild package-owned artifacts; preserve the isolated dependency cache.
build_path = root/'.lake/build'
assert not build_path.is_symlink(), 'Package build directory must not be a symlink'
if build_path.exists():
    shutil.rmtree(build_path)
assert not build_path.exists(), 'Fresh package rebuild requires successful artifact removal'
run('build', [sys.executable, 'scripts/build_serial.py'])
run('axioms', [str(prefix/'bin/lake'), 'env', 'lean', *lean_flags, 'AxiomAudit.lean'])
try:
    receipt['axiom_audit'] = check_reports((root/'AxiomAudit.lean').read_text(),
        (out/'axioms.log').read_text(), cfg['permitted_axioms'])
except ValueError as error:
    receipt['result'] = 'failed'
    receipt['axiom_audit'] = {'result': 'failed', 'error': str(error)}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    raise SystemExit('Ordered axiom validation failed: '+str(error))
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
run('native-kernel', [str(prefix/'bin/lake'), 'env', 'leanchecker', 'SECSolution'])
# Source-only protected modules are copied into a fresh root, with no original
# package source/build directory on either protected search path.
protected_root = out/'protected'
require_clean_output_tree(protected_root)
protected_root.mkdir()
protected_sources = protected_root/'ProtectedSources'
protected_sources.mkdir()
for row in protected_map['mapping']:
    shutil.copyfile(root/row['protected_source'], protected_root/row['protected_source'])
alias = protected_root/'ProtectedSparseCompletion'
alias.mkdir()
shutil.copyfile(root/'SECChallenge.lean', alias/'Challenge.lean')
protected_env = env | {'LEAN_PATH': ':'.join([str(protected_root)]+dependency_paths),
                       'LEAN_SRC_PATH': ':'.join([str(protected_root), str(prefix/'src/lean'), str(prefix/'src/lean/lake')]+list(map(str, deps)))}
protected_plan = {'source_map': protected_map,
    'source_files': [file_record(path) for path in sorted(protected_root.rglob('*.lean'))],
    'order': protected_map['protected_build_order']+['ProtectedSparseCompletion.Challenge'],
    'environment': {key: protected_env[key] for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_NUM_THREADS']}}
(out/'protected-plan.json').write_text(json.dumps(protected_plan, indent=2)+'\n')
receipt['protected_plan'] = file_record(out/'protected-plan.json')
phase_log = out/'protected-compile.log'
phase_log.write_text('Serial protected source compilation; individual logs are recorded below.\n')
phase = {'name': 'protected-compile', 'kind': 'serial-command-group', 'exit_code': None, 'commands': [], 'cwd': str(protected_root)}
receipt['checks'].append(phase)
(out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
phase_start = time.monotonic()
for index, name in enumerate(protected_plan['order']):
    relative = Path(name.replace('.', '/'))
    source_path = protected_root/relative.with_suffix('.lean')
    output_path = protected_root/relative.with_suffix('.olean')
    # Every own artifact is genuinely emitted by this stage; no stale fallback.
    assert not any((protected_root/Path(str(relative)+suffix)).exists() for suffix in FACETS), 'Stale protected artifact refused'
    argv = [str(prefix/'bin/lean'), *lean_flags, '-o', str(output_path), str(source_path)]
    log_path = out/f'protected-{index:03d}-{name}.log'
    started = time.monotonic()
    with log_path.open('w') as log:
        result = subprocess.run(argv, cwd=protected_root, env=protected_env, stdout=log, stderr=subprocess.STDOUT)
    command = {'module': name, 'argv': argv, 'cwd': str(protected_root), 'exit_code': result.returncode,
               'elapsed_seconds': round(time.monotonic()-started, 3), 'source': file_record(source_path),
               'log': file_record(log_path)}
    phase['commands'].append(command)
    with phase_log.open('a') as summary:
        summary.write(f'{index+1}/{len(protected_plan["order"])} {name} exit={result.returncode} log={log_path.name}\n')
    phase['log_sha256'] = file_record(phase_log)['sha256']
    if result.returncode:
        phase['exit_code'] = result.returncode
        receipt['result'] = 'failed'
        (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
        raise SystemExit(result.returncode)
    command['outputs'] = [file_record(protected_root/Path(str(relative)+suffix)) for suffix in FACETS]
    (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('protected-module', index+1, '/', len(protected_plan['order']), name, flush=True)
phase.update(exit_code=0, elapsed_seconds=round(time.monotonic()-phase_start, 3))
(out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
ch, sol = out/'challenge.ndjson', out/'solution.ndjson'
run('challenge-export', [str(prefix/'bin/leanexport'), 'ProtectedSparseCompletion.Challenge', '--', *targets], protected_root, protected_env, ch)
run('solution-export', [str(prefix/'bin/lake'), 'env', 'leanexport', 'SECSolution', '--', *targets], root, env, sol)
run('pinned-comparator-and-negative-control', [str(prefix/'bin/lean'), *lean_flags, '--run', str(root/'scripts/CompareExports.lean'), str(ch), str(sol), *cfg['theorem_names']])
run('export-native-kernel', [str(prefix/'bin/leanchecker'), '--silent', '--from-export', str(sol)])
for path in [ch, sol]:
    receipt.setdefault('exports', {})[path.name] = {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}
assert hashes == {f:hashlib.sha256((repo/f).read_bytes()).hexdigest() for f in files}
assert tool_hashes == {f:hashlib.sha256((repo/f).read_bytes()).hexdigest() for f in tool_paths}
assert not subprocess.check_output(['git', 'status', '--porcelain', '--', *tool_paths], cwd=repo, text=True)
assert not subprocess.check_output(['git', 'status', '--porcelain', '--', str(root)], cwd=repo, text=True)
# Reauthenticate every dependency after all build/export/checker execution.
for dep in json.loads((root/'lake-manifest.json').read_text())['packages']:
    path = root/'.lake/packages'/dep['name']
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip() == dep['rev']
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=path, text=True)
# Bind freshly generated proof and evaluator sidecars as well as source bytes.
receipt['package_build_artifacts'] = {
    str(path.relative_to(root)): {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}
    for path in sorted((root/'.lake/build').rglob('*'))
    if path.is_file() and path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'))}
receipt['protected_build_artifacts'] = {
    str(path.relative_to(out)): {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}
    for path in sorted(protected_root.rglob('*'))
    if path.is_file() and path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'))}
# Re-resolve runtime/compiler and all loaded cached inputs after all stages.
inputs_after = capture_inputs(root, prefix, input_source_files, input_extra_files)
(out/'inputs-after.json').write_text(json.dumps(inputs_after, indent=2)+'\n')
receipt['inputs_after'] = file_record(out/'inputs-after.json')
receipt['inputs_unchanged'] = inputs_before == inputs_after
assert receipt['inputs_unchanged'], 'Source/facet/runtime input envelope changed'
assert protected_plan['source_files'] == [file_record(path) for path in sorted(protected_root.rglob('*.lean'))]
for command in phase['commands']:
    assert command['outputs'] == [file_record(item['path']) for item in command['outputs']], 'Protected output changed after emission'
receipt['result']='pass'
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
