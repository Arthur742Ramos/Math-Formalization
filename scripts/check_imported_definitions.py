"""Audit retained material imported definitions; never fetch, build or claim completeness.

Default mode checks self-consistency. --dependency-root additionally compares
every excerpt/full-file digest against the exact pinned clean Git checkout.
Independent review owns inventory completeness and mathematical interpretation;
actual Lean compilation owns the checked-bridge claims.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def local_file(root, name):
    parts = pathlib.PurePosixPath(name)
    require(not parts.is_absolute() and parts.parts and
            all(p not in {'..', '.'} for p in parts.parts), 'Unsafe evidence path')
    file = root
    for part in parts.parts:
        file = file / part
        require(not file.is_symlink(), 'Symlink in evidence path')
    require(file.is_file() and file.resolve().is_relative_to(root.resolve()),
            'Missing evidence file: ' + name)
    return file


def declaration_head_matches(name, kind, body, *, legacy=False):
    """Match the complete retained declaration name, including a trailing prime."""
    terminal = re.escape(name.split('.')[-1]) + r"(?![\w'!?.])"
    # Lean's `class inductive` remains an inductive declaration with a class attribute.
    # Only this exact modifier is accepted, and only for the inductive kind.
    kind_prefix = r"(?:class )?inductive" if kind == 'inductive' else re.escape(kind)
    prefix = r'(?m)^def ' if legacy else (
        r"(?m)^(?:@\[[^\n]*\] )?(?:protected )?(?:noncomputable )?" + kind_prefix +
        r" (?:[A-Za-z_][\w']*\.)*")
    return bool(re.search(prefix + terminal, body))


GENERATED_PAIRS = {
    ('mabs', 'abs'): 'Mathlib/Algebra/Order/Group/Unbundled/Abs.lean',
    ('Pi.mulSingle', 'Pi.single'): 'Mathlib/Algebra/Notation/Pi/Basic.lean',
}
GENERATED_BRIDGES = {
    ('mabs', 'abs'): 'generated_abs_rational_semantics',
    ('Pi.mulSingle', 'Pi.single'): 'generated_single_real_semantics',
}


def strip_lean_comments_and_strings(text):
    """Mask nested comments and strings, preserving offsets and line boundaries."""
    result = list(text)
    i, depth, string, raw_end = 0, 0, False, None
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                result[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': result[i] = ' '
                i += 1
        elif raw_end:
            if text.startswith(raw_end, i):
                result[i:i+len(raw_end)] = ' ' * len(raw_end)
                i += len(raw_end); raw_end = None
            else:
                if text[i] != '\n': result[i] = ' '
                i += 1
        elif string:
            char = text[i]
            if char != '\n': result[i] = ' '
            if char == '\\' and i+1 < len(text):
                if text[i+1] != '\n': result[i+1] = ' '
                i += 2
            else:
                if char == '"': string = False
                i += 1
        elif text.startswith('/-', i):
            result[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                result[i] = ' '; i += 1
        elif text[i] == '"':
            result[i] = ' '; string = True; i += 1
        elif text[i] == 'r' and (i == 0 or not (text[i-1].isalnum() or text[i-1] == '_')):
            match = re.match(r'r(#+)?"', text[i:])
            if match:
                raw_end = '"' + (match.group(1) or '')
                result[i:i+len(match[0])] = ' ' * len(match[0]); i += len(match[0])
            else:
                i += 1
        else:
            i += 1
    if depth or string or raw_end:
        raise ValueError('Unterminated retained Lean comment/string')
    return ''.join(result)


def generated_definition_bridge(declaration, body, source_path, attestation,
                                compiler_commit, mathlib_commit):
    def require(condition, message):
        if not condition: raise ValueError(message)
    target = declaration['name']
    generated = declaration['generated_from']
    generator = generated['generator_name']
    require((generator, target) in GENERATED_PAIRS and
            source_path == GENERATED_PAIRS[(generator, target)],
            'Unapproved generated source/target/path')
    require(declaration['declaration_kind'] == 'def' and
            generated['generator_declaration_kind'] == 'def' and
            generated['producer_attribute'] == 'to_additive' and
            generated['expected_target_name'] == target and
            generated['generator_excerpt'] == declaration['definition_excerpt'] and
            declaration['bridge_kind'] == 'proved-equivalence',
            'Generated definition metadata mismatch')
    clean = strip_lean_comments_and_strings(body)
    terminal = (r"(?:" + re.escape(generator) + "|" +
                re.escape(generator.split('.')[-1]) + r")(?![\w'!?.])")
    # These exact producers use unnamed output and only this retained attr option.
    # Reject other producer identifiers, explicit target arguments and options.
    head = (r'(?m)^\s*@\[\s*to_additive\s*(?:\(attr\s*:=\s*grind\))?\s*\]\s*'
            r'(?:protected )?(?:noncomputable )?def ' + terminal)
    require(bool(re.search(head, clean)), 'Missing attached to_additive generator head')
    evidence = generated['generated_declaration_evidence']
    require(evidence['exact_exported_name'] == target and
            evidence['declaration_kind'] == 'def', 'Generated target evidence mismatch')
    require(type(attestation['schema_version']) is int and attestation['schema_version'] == 1 and
            attestation['compiler_commit'] == compiler_commit and
            attestation['mathlib_commit'] == mathlib_commit,
            'Generated target evidence pin mismatch')
    for entry in ['challenge.ndjson', 'solution.ndjson']:
        export = attestation['exports'][entry]
        require(bool(re.fullmatch(r'[0-9a-f]{64}', export['sha256'])) and
                type(export['bytes']) is int and export['bytes'] > 0,
                'Invalid generated declaration export binding')
        record = export['declarations'][target]
        require(record['kind'] == 'def' and record['resolved_name'] == target and
                bool(re.fullmatch(r'[0-9a-f]{64}', record['raw_record_sha256'])) and
                all(type(record[k]) is int and record[k] >= 0 for k in
                    ['name_id', 'type_expression_root', 'value_expression_root']),
                'Missing generated definition in pinned dual export evidence')
    bridge = generated['checked_semantic_bridge']
    require(bridge == GENERATED_BRIDGES[(generator, target)],
            'Invalid generated semantic bridge name')
    return bridge


def check(project, dependency_root=None):
    project = pathlib.Path(project)
    manifest_file = local_file(project, 'verification/material-imported-definitions.json')
    data = json.loads(manifest_file.read_text())
    version = data['schema_version']
    require(version in {1, 2}, 'Unknown imported-definition schema')
    dep = data['dependency']
    pin = dep['commit']
    require(re.fullmatch(r'[0-9a-f]{40}', pin), 'Non-exact dependency commit')
    require(re.fullmatch(r'https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', dep['repository']),
            'Invalid dependency repository')
    lock = json.loads(local_file(project, 'lake-manifest.json').read_text())
    matches = [p for p in lock['packages'] if p['name'] == dep['name']]
    require(len(matches) == 1 and matches[0]['rev'] == pin and
            matches[0]['url'].removesuffix('.git') == dep['repository'], 'Dependency lock mismatch')
    require(local_file(project, 'lean-toolchain').read_text().strip() == dep['lean_toolchain'],
            'Toolchain mismatch')
    config = json.loads(local_file(project, 'comparator.json').read_text())
    selected = set(config['theorem_names']) | set(config['definition_names'])
    inventory = data['required_declarations']
    require(inventory and len(inventory) == len(set(inventory)), 'Empty or duplicate material inventory')
    declarations = data['material_declarations']
    names = [d['name'] for d in declarations]
    require(len(names) == len(set(names)) and set(names) == set(inventory),
            'Missing or duplicate material definition evidence')
    document = local_file(project, data['documentation']).read_text()
    excerpts = {}
    excerpt_paths = {}
    generated_bridges = []
    paths = set()
    source_count = 0
    for source in data['source_files']:
        path = source['path']
        parts = pathlib.PurePosixPath(path)
        require(not parts.is_absolute() and parts.parts and '..' not in parts.parts and
                path not in paths, 'Unsafe or duplicate upstream path')
        paths.add(path)
        require(source['url'] == f'{dep["repository"]}/blob/{pin}/{path}', 'Non-pinned upstream URL')
        require(re.fullmatch(r'[0-9a-f]{64}', source['sha256']) and
                re.fullmatch(r'[0-9a-f]{40}', source['git_blob_sha1']), 'Invalid upstream digest')
        require(source['license'] == 'Apache-2.0' and source['upstream_header'].startswith('/-\n')
                and 'Copyright' in source['upstream_header'] and
                'Apache 2.0' in source['upstream_header'], 'Missing upstream attribution')
        origin = None
        if dependency_root is not None:
            dep_root = pathlib.Path(dependency_root)
            def git(*args):
                return subprocess.check_output(['git', '-C', str(dep_root), *args])
            require(git('rev-parse', 'HEAD').decode().strip() == pin, 'Checkout not at exact pin')
            require(not git('status', '--porcelain', '--', path).strip(), 'Modified upstream source')
            origin = git('show', pin + ':' + path)
            working = local_file(dep_root, path).read_bytes()
            require(origin == working, 'Dependency worktree differs from pinned source')
            blob = hashlib.sha1(b'blob ' + str(len(origin)).encode() + b'\0' + origin).hexdigest()
            require(sha(origin) == source['sha256'] and blob == source['git_blob_sha1'],
                    'Full upstream source digest mismatch')
            require(origin.startswith(source['upstream_header'].encode()), 'Upstream header mismatch')
            source_count += 1
        require(source['url'] in document and source['sha256'] in document and
                source['upstream_header'] in document, 'Documentation missing source evidence')
        for excerpt in source['excerpts']:
            name = excerpt['name']
            require(name not in excerpts, 'Duplicate excerpt')
            first, last = excerpt['first_line'], excerpt['last_line']
            require(type(first) is int and type(last) is int and 1 <= first <= last,
                    'Invalid excerpt range')
            text = excerpt['text']
            require(text.endswith('\n') and len(text.splitlines()) == last - first + 1 and
                    sha(text.encode()) == excerpt['sha256'], 'Excerpt bytes/range mismatch')
            require(excerpt['url'] == source['url'] + f'#L{first}-L{last}', 'Excerpt locator mismatch')
            require(text in document and excerpt['url'] in document, 'Documentation missing excerpt')
            if origin is not None:
                expected = b''.join(origin.splitlines(keepends=True)[first - 1:last])
                require(expected == text.encode(), 'Excerpt differs from exact pinned source')
            excerpts[name] = text
            excerpt_paths[name] = path
    require(paths, 'Missing upstream sources')
    for declaration in declarations:
        name = declaration['name']
        roles = {'hypothesis', 'conclusion', 'definition'}
        if version == 2:
            roles |= {'hypothesis-and-conclusion', 'proof-dependency'}
        require(declaration['role'] in roles and
                declaration['meaning'].strip() and name in document, 'Missing semantic account')
        usage = declaration['used_by']
        require(usage and len(usage) == len(set(usage)) and set(usage) <= selected,
                'Missing or invalid selected-declaration coverage')
        require(all(n in document for n in usage), 'Document omits affected declarations')
        body = excerpts[declaration['definition_excerpt']]
        if version == 1:
            require(declaration_head_matches(name, 'def', body, legacy=True),
                    'Definition evidence is not a definition')
            require(declaration['bridge_kind'] == 'proved-equivalence',
                    'Semantic bridge must not be claimed as definitional equality')
            for key in ['semantic_bridge_excerpt', 'complement_excerpt']:
                require(declaration[key] in excerpts, 'Missing semantic/complement bridge')
        else:
            kind = declaration['declaration_kind']
            require(kind in {'def', 'class', 'structure', 'inductive'}, 'Unknown declaration kind')
            if 'generated_from' in declaration:
                generated = declaration['generated_from']
                evidence = generated['generated_declaration_evidence']
                evidence_file = local_file(project, evidence['path'])
                require(sha(evidence_file.read_bytes()) == evidence['sha256'],
                        'Generated target attestation digest mismatch')
                core = json.loads(local_file(project, 'verification/lean-core-definitions.json').read_text())
                generated_bridges.append(generated_definition_bridge(
                    declaration, body, excerpt_paths[declaration['definition_excerpt']],
                    json.loads(evidence_file.read_text()), core['compiler_commit'], pin))
                linked = [x for x in data.get('generated_declarations', []) if x['name'] == name]
                require(len(linked) == 1 and linked[0]['source'] == generated['generator_excerpt'] and
                        linked[0]['mechanism'] == 'to_additive' and
                        linked[0]['generator_name'] == generated['generator_name'] and
                        linked[0]['checked_bridge'] == generated['checked_semantic_bridge'],
                        'Generated declaration mechanism linkage mismatch')
            else:
                require(declaration_head_matches(name, kind, body),
                        'Pinned declaration kind/name mismatch')
            bridge = declaration['bridge_kind']
            allowed = {'class-fields'} if kind in {'class', 'structure'} else {
                'literal-unfolding', 'proved-equivalence'}
            require(bridge in allowed, 'Incorrect literal/class/proved bridge kind')
            refs = declaration['bridge_excerpts']
            require(refs and len(refs) == len(set(refs)) and all(n in excerpts for n in refs),
                    'Missing or invalid semantic bridge evidence')
            require(declaration['dependency_expansion'].strip() and
                    declaration['proof_status'].strip(), 'Missing dependency or proof-status account')
    lake = tomllib.loads(local_file(project, 'lakefile.toml').read_text())
    modules = data['checked_bridge_modules']
    require(len(modules) >= 2 and len({m['module'] for m in modules}) == len(modules),
            'Missing independent bridge modules')
    entrypoints = set()
    for module in modules:
        require(module['path'] == module['module'].replace('.', '/') + '.lean' and
                module['module'] in lake['defaultTargets'], 'Bridge module not built by default')
        b = local_file(project, module['path']).read_bytes()
        require(sha(b) == module['sha256'], 'Bridge module digest mismatch')
        body = b.decode()
        for bridge in generated_bridges:
            require(declaration_head_matches(bridge, 'theorem', strip_lean_comments_and_strings(body)),
                    'Missing named generated semantic bridge in checked module')
        for field in ['challenge_module', 'solution_module']:
            if re.search(r'(?m)^public import ' + re.escape(config[field]) + r'$', body):
                entrypoints.add(field)
        require(not all(re.search(r'(?m)^public import ' + re.escape(config[f]) + r'$', body)
                        for f in ['challenge_module', 'solution_module']), 'Mixed duplicate entrypoints')
        require('-- BEGIN material-imported-definition audit' in body and
                '-- END material-imported-definition audit' in body, 'Missing checked bridge block')
    require(entrypoints == {'challenge_module', 'solution_module'}, 'Missing entrypoint bridge coverage')
    return dict(status='pass', project=str(project), material_declarations=names,
                retained_source_files=len(paths), retained_excerpts=len(excerpts),
                upstream_origin='exact-pinned-clean-Git-source' if dependency_root else 'not-checked',
                upstream_files_authenticated=source_count, bridge_compilation='separate actual Lean build required',
                scope='Retained evidence consistency; inventory completeness and mathematical fidelity require independent review.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-path', default='topology/kuratowski-ulam')
    parser.add_argument('--dependency-root', type=pathlib.Path)
    args = parser.parse_args()
    project = pathlib.Path(args.project_path)
    print(json.dumps(check(project if project.is_absolute() else ROOT / project,
                           args.dependency_root), indent=2))
