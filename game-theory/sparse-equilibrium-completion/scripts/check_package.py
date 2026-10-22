#!/usr/bin/env python3
"""Local foundation consistency checks; no claim of mathematical completeness."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
cfg = json.loads((root / 'comparator.json').read_text())
source = (root / 'SparseCompletion.lean').read_text()
challenge = (root / 'SECChallenge.lean').read_text()
assert source == challenge, 'Protected Challenge must contain the exact fixed public definitions and proofs'
for filename in ['SparseCompletion.lean', 'SECChallenge.lean', 'SECSolution.lean', 'AxiomAudit.lean']:
    text = (root / filename).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', text), filename
    assert not re.search(r'^private\s', text, re.M), filename
for name in cfg['theorem_names']:
    assert re.search(r'^theorem ' + re.escape(name.split('.')[-1]) + r'\b', source, re.M), name
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
files = [p for p in root.rglob('*') if p.is_file() and '.lake' not in p.parts
         and p.suffix not in ['.olean', '.ilean', '.log'] and '__pycache__' not in p.parts]
print(json.dumps({'check': 'foundation-source-consistency', 'result': 'pass',
    'selected_theorems': cfg['theorem_names'],
    'sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},
    'limits': 'Not a proof build, source-fidelity review, canonical verifier, or release clearance'}, indent=2))
