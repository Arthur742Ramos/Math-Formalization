#!/usr/bin/env python3
"""Source-only protected copies: exact canonical bytes except own import tokens.

Module boundaries are preserved to avoid cross-module elaborator cache reuse.
No declaration or exported-name normalization is performed.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tomllib

if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('Protected source checks refuse optimized Python')

from assemble_challenge import MODULES

PIN_SHA256 = '26912f81e3b3f3a03d154464929b2363d8940679c6f09fdc159ed5eabbed77c0'
COMPARATOR_SHA256 = '9a873345c928d8b543b0bdcd7ea03ce667fea59abb35853435fab52d0f7b042b'
COMPARE_EXPORTS_SHA256 = 'b0bd1132246f4d7ecc6531c3a1897ce832c701e74fb0ce9fd572c4550a1a1877'
FACETS = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')
NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
RAW_STRING = re.compile(r'r(#+)"')
CHARACTER = re.compile(r"'(?:\\.|[^'\\\n])'")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def mask_comments_strings(text):
    """Retain character offsets/newlines, handling nested comments and strings."""
    out = list(text)
    pos, depth = 0, 0
    while pos < len(text):
        start = pos
        if not depth and text[pos] == '«':
            end = text.find('»', pos+1)
            require(end >= 0, 'Unclosed quoted identifier')
            pos = end+1
        elif not depth and text[pos] == "'" and CHARACTER.match(text, pos):
            pos += len(CHARACTER.match(text, pos)[0])
        elif text.startswith('/-', pos):
            depth += 1; pos += 2
        elif depth and text.startswith('-/', pos):
            depth -= 1; pos += 2
        elif depth:
            pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        elif text[pos] == '"' or RAW_STRING.match(text, pos):
            raw = RAW_STRING.match(text, pos)
            marker = '"' + raw[1] if raw else '"'
            pos += len(raw[0]) if raw else 1
            while pos < len(text):
                if text.startswith(marker, pos):
                    pos += len(marker); break
                pos += 2 if not raw and text[pos] == '\\' else 1
            else:
                raise ValueError('Unclosed string')
        else:
            pos += 1
            continue
        for index in range(start, min(pos, len(text))):
            if out[index] not in '\r\n':
                out[index] = ' '
    require(depth == 0, 'Unclosed comment')
    return ''.join(out)


def header_imports(data):
    """Ordered (module,start,end) import tokens; refuse unsupported headers."""
    text = data.decode('utf-8')
    masked = mask_comments_strings(text)
    result, offset = [], 0
    for line in masked.splitlines(keepends=True):
        clean = line.strip()
        if not clean or clean in ('module', 'prelude'):
            offset += len(line); continue
        match = re.fullmatch(r'\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*', line)
        if not match:
            require(not re.match(r'\s*(?:(?:public|private|meta)\s+)*import\b', line),
                    'Unsupported import header: ' + clean)
            break
        for token in re.finditer(r'\S+', match[1]):
            value = token[0]
            if value == 'all':
                continue
            require(NAME.fullmatch(value), 'Unsupported import token: ' + value)
            begin = offset + match.start(1) + token.start()
            result.append((value, begin, begin + len(value)))
        offset += len(line)
    return result


def import_names(data):
    return [name for name, _, _ in header_imports(data)]


def transform(data):
    text = data.decode('utf-8')
    for name, start, end in reversed(header_imports(data)):
        if name in MODULES:
            text = text[:start] + 'ProtectedSources.' + text[start:end] + text[end:]
    return text.encode('utf-8')


def canonical_rows(root):
    require(digest((root/'comparator.json').read_bytes()) == COMPARATOR_SHA256,
            'Fixed 1742-contract comparator configuration changed')
    require(digest((root/'scripts/CompareExports.lean').read_bytes()) == COMPARE_EXPORTS_SHA256,
            'Pinned comparison/negative-control driver changed')
    raw = (root/'verification/protected-canonical-sources.json').read_bytes()
    require(digest(raw) == PIN_SHA256, 'Canonical source pin manifest changed')
    manifest = json.loads(raw)
    rows = manifest['modules']
    require(len(rows) == len(MODULES) == 373, 'Exactly 373 canonical modules required')
    require([row['module'] for row in rows] == MODULES, 'Canonical module order/bijection changed')
    require(len(set(MODULES)) == 373, 'Duplicate canonical module')
    for row in rows:
        name = row['module']
        require(row['source'] == name+'.lean' and row['protected_source'] == 'ProtectedSources/'+name+'.lean'
                and row['protected_module'] == 'ProtectedSources.'+name, 'Invalid source mapping')
        require(digest((root/row['source']).read_bytes()) == row['canonical_sha256'],
                'Canonical source differs from frozen 89f: '+name)
    return rows


def aggregate():
    return ('module\n'+''.join('public import ProtectedSources.'+name+'\n' for name in MODULES)).encode()


def checked_graph(sources):
    """Topological order of exact local imports, preserving each header order."""
    order, visiting, visited = [], set(), set()
    def visit(name):
        require(name not in visiting, 'Cyclic local imports: '+name)
        if name in visited:
            return
        visiting.add(name)
        for dep in import_names(sources[name]):
            if dep in sources:
                visit(dep)
        visiting.remove(name); visited.add(name); order.append(name)
    for name in sources:
        visit(name)
    return order


def validate(root):
    rows = canonical_rows(root)
    config = tomllib.loads((root/'lakefile.toml').read_text())
    libraries = [lib for lib in config.get('lean_lib', []) if lib.get('name') == 'ProtectedSources']
    require(len(libraries) == 1 and libraries[0].get('globs') == ['ProtectedSources.+'],
            'ProtectedSources library must select exactly submodules with ProtectedSources.+')
    require(not (root/'ProtectedSources.lean').exists() and not (root/'ProtectedSources.lean').is_symlink(),
            'ProtectedSources root module must be absent; only 373 copied submodules are allowed')
    directory = root/'ProtectedSources'
    require(directory.is_dir() and not directory.is_symlink(), 'Protected source directory missing/symlink')
    actual = sorted(str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file())
    require(actual == sorted(row['module']+'.lean' for row in rows), 'Missing/unexpected protected copies or artifacts')
    graph, mapping = {}, []
    for row in rows:
        source = (root/row['source']).read_bytes()
        copy = root/row['protected_source']
        require(not copy.is_symlink(), 'Protected copy symlink: '+str(copy))
        data = copy.read_bytes()
        require(data == transform(source), 'Protected body/import-token mismatch: '+row['module'])
        expected = [('ProtectedSources.'+name if name in MODULES else name) for name in import_names(source)]
        require(import_names(data) == expected, 'Protected import graph mismatch')
        require(not set(import_names(data)) & set(MODULES), 'Original project import leakage')
        graph[row['protected_module']] = data
        mapping.append(row | {'protected_sha256': digest(data), 'imports': expected})
    require((root/'SECChallenge.lean').read_bytes() == aggregate(), 'Challenge must aggregate only exact protected imports')
    order = checked_graph(graph)
    return {'canonical_commit': '89f353b412f612555265cf902844107522d595b3',
            'canonical_modules': 373, 'protected_copies': 373, 'mapping': mapping,
            'protected_library': {'name': 'ProtectedSources', 'globs': ['ProtectedSources.+'],
                                  'matched_modules': list(graph), 'root_module_present': False},
            'protected_build_order': order, 'aggregator_sha256': digest(aggregate()),
            'limits': 'Source identity only; private generated names and pinned full comparison require fresh execution.'}


def discover_sources(root):
    paths = [p for p in root.rglob('*.lean') if '.lake' not in p.relative_to(root).parts
             and '__pycache__' not in p.parts]
    return {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in paths}


def require_clean_output_tree(directory):
    require(not directory.exists() and not directory.is_symlink(),
            'Fresh protected output directory required; stale artifact/tree refused')


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    print(json.dumps(validate(root), indent=2))
