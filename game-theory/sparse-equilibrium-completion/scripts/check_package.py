#!/usr/bin/env python3
"""Local foundation consistency checks; no claim of mathematical completeness."""
import hashlib
import json
from pathlib import Path
import re
import sys
import subprocess

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Source checks refuse assertion-disabled Python optimization modes')

from assemble_challenge import assemble, MODULES

root = Path(__file__).resolve().parents[1]
cfg = json.loads((root / 'comparator.json').read_text())
source = (root / 'SparseCompletion.lean').read_text()
challenge = (root / 'SECChallenge.lean').read_text()
assert challenge == assemble(root), 'Challenge must contain the exact assembled public source bodies'
all_source = '\n'.join((root/(name+'.lean')).read_text() for name in MODULES)
for filename in [name+'.lean' for name in MODULES] + ['SECChallenge.lean', 'SECSolution.lean', 'AxiomAudit.lean']:
    text = (root / filename).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', text), filename
    assert not re.search(r'^private\s', text, re.M), filename
for name in cfg['theorem_names']:
    assert re.search(r'^theorem ' + re.escape(name.split('.')[-1]) + r'\b', all_source, re.M), name
assert cfg['definition_names'] == [], 'All model definitions are fixed; there are no definition holes'
assert cfg['permitted_axioms'] == ['propext', 'Quot.sound', 'Classical.choice']
assert (root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
manifest = json.loads((root / 'lake-manifest.json').read_text())
assert manifest['name'] == 'sparseEquilibriumCompletion'
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
assert mathlib['rev'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
metadata = json.loads((root / 'metadata.draft.json').read_text())
assert metadata['submission_ready'] is False
assert metadata['formalization_authors'] == metadata['responsible_maintainers'] == []
assert metadata['paper_commit'] == '1a424f297925294ae5818ff1ee7512304af1d460'
core = json.loads((root/'verification/lean-core-definitions.json').read_text())
assert core['compiler_commit'] == '11acb17ec6b07a8f9e9173e6845197929540936b'
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
core_bytes = (prefix/'src/lean/Init/Prelude.lean').read_bytes()
assert hashlib.sha256(core_bytes).hexdigest() == core['source_sha256']
assert hashlib.sha1(b'blob '+str(len(core_bytes)).encode()+b'\0'+core_bytes).hexdigest() == core['github_blob_sha1']
core_excerpt = b''.join(core_bytes.splitlines(keepends=True)[core['first_line']-1:core['last_line']])
assert core_excerpt == core['excerpt'].encode()
assert hashlib.sha256(core_excerpt).hexdigest() == core['excerpt_sha256']
assert core['url'] == 'https://github.com/leanprover/lean4/blob/'+core['compiler_commit']+'/'+core['path']
assert 'structure Fin (n : Nat) where' in core['excerpt'] and 'isLt : LT.lt val n' in core['excerpt']
bins = json.loads((root/'verification/lean-core-bin-definitions.json').read_text())
assert bins['compiler_commit'] == core['compiler_commit']
for evidence in bins['sources']:
    relative = evidence['path'].removeprefix('src/')
    data = (prefix/'src/lean'/relative).read_bytes()
    assert hashlib.sha256(data).hexdigest() == evidence['source_sha256']
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == evidence['github_blob_sha1']
    excerpt = b''.join(data.splitlines(keepends=True)[evidence['first_line']-1:evidence['last_line']])
    assert excerpt == evidence['excerpt'].encode()
    assert hashlib.sha256(excerpt).hexdigest() == evidence['excerpt_sha256']
    assert data.startswith(evidence['upstream_header'].encode())
    assert evidence['url'] == 'https://github.com/leanprover/lean4/blob/'+bins['compiler_commit']+'/'+evidence['path']
assert {e['name'] for e in bins['sources']} == {'Rat inversion, natural powers and division', 'Rat.neg', 'PUnit', 'Nonempty', 'Nat.sqrt and decreasing Newton iteration', 'Rat rational constants', 'Fin.cases and zero/successor contracts', 'List.decidableBAll', 'List constructors', 'List.length_ofFn', 'Unit', 'Fin.foldr', 'Rat multiplication', 'List.map', 'Option constructors', 'Function.Injective', 'List.mem_map', 'Add-and-Mul-classes', 'LE-and-LT', 'Prod-with-right-associated-tuple-convention', 'Rat.floor', 'List.ofFn', 'Decidable', 'Min-and-Max', 'Sum.elim', 'Subtype', 'List.filter', 'Rat subtraction', 'SMul-class', 'Option.map', 'Fin.induction', 'Rat addition and negation', 'Sigma', 'List.mem_ofFn', 'Sum', 'Rat comparison and decidability', 'DecidablePred', 'Nat.sqrt_le and Nat.lt_succ_sqrt', 'self-scalar-action-from-multiplication', 'Rat', 'Bool.Reflects', 'List.mem_filter', 'List.Mem and Membership', 'Rat.le_floor_iff', 'Fin.rev'}
aux = json.loads((root/'verification/auxiliary-imported-definitions.json').read_text())
aux_pin = next(p for p in manifest['packages'] if p['name'] == 'batteries')
assert aux['dependency'] == aux_pin
aux_root = root/'.lake/packages/batteries'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=aux_root, text=True).strip() == aux_pin['rev']
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=aux_root, text=True).strip()
for evidence in aux['sources']:
    data = (aux_root/evidence['path']).read_bytes()
    pinned = subprocess.check_output(['git', 'show', aux_pin['rev']+':'+evidence['path']], cwd=aux_root)
    assert data == pinned
    assert hashlib.sha256(data).hexdigest() == evidence['source_sha256']
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == evidence['github_blob_sha1']
    assert evidence['url'] == 'https://github.com/leanprover-community/batteries/blob/'+aux_pin['rev']+'/'+evidence['path']
    assert data.startswith(evidence['upstream_header'].encode())
    for record in evidence['excerpts']:
        excerpt = b''.join(data.splitlines(keepends=True)[record['first_line']-1:record['last_line']])
        assert excerpt == record['excerpt'].encode()
        assert hashlib.sha256(excerpt).hexdigest() == record['excerpt_sha256']

repo = root.parents[1]
identifier_test = repo/'scripts/test_imported_definition_identifiers.py'
identifier_run = subprocess.run([sys.executable, str(identifier_test)], cwd=repo,
    text=True, capture_output=True, check=False)
assert identifier_run.returncode == 0, identifier_run.stdout+identifier_run.stderr
identifier_controls = {'returncode': identifier_run.returncode,
    'stdout': identifier_run.stdout, 'stderr': identifier_run.stderr,
    'test_sha256': hashlib.sha256(identifier_test.read_bytes()).hexdigest(),
    'checker_sha256': hashlib.sha256((repo/'scripts/check_imported_definitions.py').read_bytes()).hexdigest()}
files = [p for p in root.rglob('*') if p.is_file() and '.lake' not in p.parts
         and p.suffix not in ['.olean', '.ilean', '.log'] and '__pycache__' not in p.parts]
print(json.dumps({'check': 'sparse-equilibrium-completion-source-consistency', 'result': 'pass',
    'selected_theorems': cfg['theorem_names'], 'identifier_regression_controls': identifier_controls,
    'sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},
    'limits': 'Not a proof build, source-fidelity review, canonical verifier, or release clearance'}, indent=2))
