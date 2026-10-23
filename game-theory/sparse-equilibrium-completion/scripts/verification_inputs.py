#!/usr/bin/env python3
"""Read-only source/facet envelope, including compiler runtime module roots.

Adapted from the independently reviewed dyadic-center runtime-v3 collector
(inventory149, internal AI-assisted source, 2026-10-23). Current cache association
is recorded; no historical upstream source-to-build provenance is invented.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from protected_sources import FACETS, import_names, require

if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('Input envelope refuses optimized Python')


def file_record(path):
    path = Path(path)
    require(path.is_file(), 'Missing required input: '+str(path))
    first = path.stat()
    hashed = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1024*1024), b''):
            hashed.update(block)
    last = path.stat()
    fields = ('st_dev', 'st_ino', 'st_size', 'st_mtime_ns', 'st_ctime_ns')
    require(tuple(getattr(first, f) for f in fields) == tuple(getattr(last, f) for f in fields),
            'Input changed while hashing: '+str(path))
    return {'path': str(path), 'real_path': str(path.resolve()),
            'sha256': hashed.hexdigest(), 'bytes': last.st_size}


def dependency_pairs(root, prefix):
    pins = json.loads((root/'lake-manifest.json').read_text())['packages']
    require(len(pins) == 9 and len({p['name'] for p in pins}) == 9, 'Exactly nine dependency pins required')
    actual = sorted(p.name for p in (root/'.lake/packages').iterdir())
    require(actual == sorted(p['name'] for p in pins), 'Unexpected/missing dependency search root')
    pairs = [(prefix/'lib/lean', prefix/'src/lean')]
    for item in sorted(pins, key=lambda p: p['name']):
        source = root/'.lake/packages'/item['name']
        pairs.append((source/'.lake/build/lib/lean', source))
    return pairs


def git_states(root):
    states = []
    for item in json.loads((root/'lake-manifest.json').read_text())['packages']:
        path = root/'.lake/packages'/item['name']
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain'], cwd=path, text=True)
        require(head == item['rev'] and not dirty, 'Dependency pin/worktree changed: '+item['name'])
        states.append({'name': item['name'], 'path': str(path), 'real_path': str(path.resolve()),
                       'head': head, 'status': dirty})
    require(len(states) == 9, 'Nine dependency Git states required')
    return states


def capture(root, prefix, source_files, extra_files):
    """Complete declared own-source graph plus target/runtime external closure.

    Package outputs are deliberately excluded: they are removed and freshly
    rebuilt, then bound separately. All loaded cached upstream facets are inputs.
    """
    root, prefix = Path(root), Path(prefix)
    pairs = dependency_pairs(root, prefix)
    own = {'.'.join(Path(p).relative_to(root).with_suffix('').parts): Path(p) for p in source_files}
    records, resolved, todo = {}, {}, ['Init', 'Lean', 'Lake']
    for name, path in sorted(own.items()):
        record = file_record(path); records[record['path']] = record
        imports = import_names(path.read_bytes())
        resolved[name] = {'own_source': record, 'imports': imports, 'fresh_outputs_excluded': True}
        todo.extend(dep for dep in imports if dep not in own)
    while todo:
        name = todo.pop()
        if name in resolved:
            continue
        relative = Path(name.replace('.', '/'))
        selected = None
        for artifacts, sources in pairs:
            if (artifacts/relative.with_suffix('.olean')).is_file():
                if artifacts == prefix/'lib/lean' and (name == 'Lake' or name.startswith('Lake.')):
                    sources = prefix/'src/lean/lake'
                selected = artifacts, sources
                break
        require(selected is not None, 'Missing external module; no fallback build: '+name)
        artifacts, sources = selected
        source = file_record(sources/relative.with_suffix('.lean'))
        records[source['path']] = source
        facets = []
        for suffix in FACETS:
            record = file_record(artifacts/Path(str(relative)+suffix))
            records[record['path']] = record; facets.append(record)
        imports = import_names(Path(source['path']).read_bytes())
        # External packages must not import original project modules.
        require(not any(dep in own for dep in imports), 'Upstream-to-project import leakage: '+name)
        resolved[name] = {'source': source, 'facets': facets, 'imports': imports,
                          'artifact_root': str(artifacts), 'source_root': str(sources)}
        todo.extend(imports)
    shared_objects = set()
    for directory in [prefix/'lib', *[sources/'.lake/build/lib' for _, sources in pairs[1:]]]:
        for path in directory.rglob('*'):
            if path.is_file() and (path.name.endswith(('.so', '.dylib', '.dll')) or '.so.' in path.name):
                shared_objects.add(path)
    for path in [*extra_files, *sorted(shared_objects)]:
        record = file_record(path); records[record['path']] = record
    return {'schema': 'native-full-input-envelope-v1', 'runtime_roots': ['Init', 'Lean', 'Lake'],
            'root_pairs': [{'artifacts': str(a), 'artifacts_real_path': str(a.resolve()),
                            'source': str(s), 'source_real_path': str(s.resolve())} for a, s in pairs],
            'git_states': git_states(root), 'resolved_modules': resolved,
            'files': dict(sorted(records.items())),
            'limits': 'Exact current source/cached fivefacet association before/after; not historical upstream build-source authentication or native/bit-cost proof.'}
