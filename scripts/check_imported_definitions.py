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


def declaration_header_matches(body, kind, name, *, legacy=False):
    """Lean identifiers may end in apostrophes, which are not Python word chars."""
    prefix = r'(?m)^def ' if legacy else (
        r'(?m)^(?:@\[[^\n]*\] )?(?:protected )?(?:noncomputable )?(?:nonrec )?' + kind +
        r" (?:[A-Za-z_][\w']*\.)*")
    return re.search(prefix + re.escape(name.split('.')[-1]) + r"(?![\w'])", body) is not None


def check_eqvgen_kind(name, kind, version):
    require(not (version == 1 and name == 'Relation.EqvGen'),
            'Relation.EqvGen requires the pinned inductive schema')
    require(version == 1 or ((name == 'Relation.EqvGen') == (kind == 'inductive')),
            'Unsupported inductive name or declaration kind')


def check_generated_sum_kind(name, kind, version):
    require(not (version == 1 and name == 'Finset.sum'),
            'Finset.sum requires pinned generated-additive evidence')
    require(version == 1 or ((name == 'Finset.sum') == (kind == 'generated_additive')),
            'Unsupported generated-additive name or declaration kind')


def check_pinned_generated_sum(declaration, dep, source, excerpt):
    """Bind this generated additive name to its exact pinned producer only."""
    require(declaration['name'] == 'Finset.sum' and
            declaration['producer'] == 'Finset.prod' and
            declaration['bridge_kind'] == 'generated-additive',
            'Unsupported generated-additive contract')
    require(dep['name'] == 'mathlib' and
            dep['repository'] == 'https://github.com/leanprover-community/mathlib4' and
            dep['commit'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55',
            'Unsupported generated-additive dependency')
    require(source['path'] == 'Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean' and
            source['sha256'] == 'e935efa96ad9381658f3158f900d04589c46d7e933cab15f4d8632e1af85527f' and
            source['git_blob_sha1'] == '0eec64f2576f4d449b44b877678fe95678cfc9f0' and
            excerpt['first_line'] == 59 and excerpt['last_line'] == 69 and
            excerpt['sha256'] == '26d8fa821bd539acece2d861933171554c86d441fbb32266ecc2ebc472639de1' and
            sha(excerpt['text'].encode()) == excerpt['sha256'],
            'Pinned generated-additive producer excerpt mismatch')


def check_real_volume_kind(name, kind, version):
    if name == 'Real.volume_eq_stieltjes_id':
        require(version == 2 and kind == 'theorem',
                'Real-volume contract requires pinned theorem evidence')


def check_pinned_real_volume(declaration, dep, source, excerpt):
    """Bind this real-volume theorem to its exact pinned source."""
    require(declaration['name'] == 'Real.volume_eq_stieltjes_id' and
            declaration['bridge_kind'] == 'proved-contract',
            'Unsupported real-volume contract')
    require(dep['name'] == 'mathlib' and
            dep['repository'] == 'https://github.com/leanprover-community/mathlib4' and
            dep['commit'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55',
            'Unsupported real-volume dependency')
    require(source['path'] == 'Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean' and
            source['sha256'] == '628bcfc45fabd59501cdebf1cc3a8003ef3aba18fc7de4710ca9ffc1033b32d7' and
            source['git_blob_sha1'] == '84794cf74fa34664073bbf336adccdefb5bada62' and
            excerpt['first_line'] == 54 and excerpt['last_line'] == 77 and
            excerpt['sha256'] == '6566b8cc0ffee203b8c49deaf5306c682ca13346166373d0168d3c951b3817a6' and
            sha(excerpt['text'].encode()) == excerpt['sha256'],
            'Pinned real-volume theorem excerpt mismatch')


def check_pinned_real_ae(source, excerpt):
    """Authenticate the separately retained almost-everywhere characterization."""
    require(source['path'] == 'Mathlib/MeasureTheory/OuterMeasure/AE.lean' and
            source['sha256'] == 'de58d3b2aa42d801e9a268df285c32e5aa6ca7ffc5b42bf5eff8f12bda87a00d' and
            source['git_blob_sha1'] == '1802fcab91bae1a8537d57413d45b28628d6d5b5' and
            excerpt['first_line'] == 132 and excerpt['last_line'] == 136 and
            excerpt['sha256'] == 'e5e156ce2adb28adce69979079b1f974df28d2d4ff50e1a81e1df2d47cafb9f4' and
            sha(excerpt['text'].encode()) == excerpt['sha256'],
            'Pinned almost-everywhere excerpt mismatch')


def check_pinned_eqvgen(declaration, dep, source, excerpt):
    """A narrow representation of one pinned inductive; not semantic validation."""
    require(declaration['name'] == 'Relation.EqvGen' and
            declaration['bridge_kind'] == 'inductive-constructors' and
            declaration['constructors'] == ['rel', 'refl', 'symm', 'trans'],
            'Unsupported inductive contract')
    require(dep['name'] == 'mathlib' and
            dep['repository'] == 'https://github.com/leanprover-community/mathlib4' and
            dep['commit'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55',
            'Unsupported inductive dependency')
    require(source['path'] == 'Mathlib/Logic/Relation.lean' and
            source['sha256'] == '2b678f33904c7e073de526d9d3243909e5d7d72bc0eed7f4cf9e65f443b72547' and
            source['git_blob_sha1'] == '173394c4bb2a511bb02a538e31a015e9393eb7b5' and
            excerpt['first_line'] == 408 and excerpt['last_line'] == 417 and
            excerpt['sha256'] == 'c22edd47d0fe6052783b4dc8ed85c4f7a58a9bb3e0fa5989d14990181b4da46a' and
            sha(excerpt['text'].encode()) == excerpt['sha256'],
            'Pinned inductive source/constructor excerpt mismatch')


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
    excerpt_evidence = {}
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
            excerpt_evidence[name] = (source, excerpt)
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
            check_eqvgen_kind(name, 'def', version)
            check_generated_sum_kind(name, 'def', version)
            check_real_volume_kind(name, 'def', version)
            require(declaration_header_matches(body, 'def', name, legacy=True),
                    'Definition evidence is not a definition')
            require(declaration['bridge_kind'] == 'proved-equivalence',
                    'Semantic bridge must not be claimed as definitional equality')
            for key in ['semantic_bridge_excerpt', 'complement_excerpt']:
                require(declaration[key] in excerpts, 'Missing semantic/complement bridge')
        else:
            kind = declaration['declaration_kind']
            require(kind in {'def', 'abbrev', 'class', 'structure', 'instance', 'theorem', 'irreducible_def', 'inductive', 'generated_additive'}, 'Unknown declaration kind')
            check_eqvgen_kind(name, kind, version)
            check_generated_sum_kind(name, kind, version)
            check_real_volume_kind(name, kind, version)
            if kind == 'inductive':
                source, excerpt = excerpt_evidence[declaration['definition_excerpt']]
                check_pinned_eqvgen(declaration, dep, source, excerpt)
            if kind == 'generated_additive':
                source, excerpt = excerpt_evidence[declaration['definition_excerpt']]
                check_pinned_generated_sum(declaration, dep, source, excerpt)
            if name == 'Real.volume_eq_stieltjes_id':
                source, excerpt = excerpt_evidence[declaration['definition_excerpt']]
                check_pinned_real_volume(declaration, dep, source, excerpt)
            require(declaration_header_matches(body, 'def' if kind == 'generated_additive' else kind,
                                               declaration['producer'] if kind == 'generated_additive' else name),
                    'Pinned declaration kind/name mismatch')
            bridge = declaration['bridge_kind']
            allowed = ({'generated-additive'} if kind == 'generated_additive' else
                       {'inductive-constructors'} if kind == 'inductive' else
                       {'class-fields'} if kind in {'class', 'structure'} else
                       {'proved-contract'} if kind == 'theorem' else
                       {'proved-equivalence'} if kind == 'irreducible_def' else
                       {'literal-unfolding', 'proved-equivalence'})
            require(bridge in allowed, 'Incorrect literal/class/proved bridge kind')
            refs = declaration['bridge_excerpts']
            require(refs and len(refs) == len(set(refs)) and all(n in excerpts for n in refs),
                    'Missing or invalid semantic bridge evidence')
            if name in {'Finset.sum', 'Real.volume_eq_stieltjes_id'}:
                require(declaration['definition_excerpt'] in refs,
                        'Material bridge omits its pinned declaration excerpt')
            if name == 'Real.volume_eq_stieltjes_id':
                require('AE_null_complement_contract' in refs,
                        'Real-volume bridge omits its almost-everywhere excerpt')
                check_pinned_real_ae(*excerpt_evidence['AE_null_complement_contract'])
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
        for field in ['challenge_module', 'solution_module']:
            if re.search(r'(?m)^public import ' + re.escape(config[field]) + r'$', body):
                entrypoints.add(field)
        require(not all(re.search(r'(?m)^public import ' + re.escape(config[f]) + r'$', body)
                        for f in ['challenge_module', 'solution_module']), 'Mixed duplicate entrypoints')
        require('-- BEGIN material-imported-definition audit' in body and
                '-- END material-imported-definition audit' in body, 'Missing checked bridge block')
        # These are structural checks only. Elaborating both modules and independently
        # checking the explicit contract types remains a separate required gate.
        required_contracts = []
        if 'Finset.sum' in names:
            required_contracts += ['generated_sum_contract', 'finite_univ_sum_contract']
        if 'Real.volume_eq_stieltjes_id' in names:
            required_contracts += ['real_volume_contract', 'ae_real_volume_contract']
        for contract in required_contracts:
            require(re.search(r'(?m)^theorem ' + re.escape(contract) + r'\b', body) and
                    re.search(r'(?m)^#print axioms ' + re.escape(contract) + r'$', body),
                    'Bridge missing named contract or axiom audit: ' + contract)
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
