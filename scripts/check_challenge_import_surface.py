"""Detect direct project-local Challenge imports under supplied source roots.

This is an early diagnostic, not the verifier's protected compilation or
transitive provenance audit. Supply every project source root, including any
non-default Lake srcDir. It cannot infer dynamic Lake configuration.
"""
import argparse
import json
from pathlib import Path
import subprocess


def direct_imports(header):
    entries = header.get('imports')
    if not isinstance(entries, list) or len(entries) != 1:
        raise ValueError('Expected exactly one Lean header result')
    item = entries[0]
    if not isinstance(item, dict) or item.get('errors') != []:
        raise ValueError('Lean reported header errors')
    result = item.get('result')
    if not isinstance(result, dict) or result.get('isModule') is not True:
        raise ValueError('Challenge must use Lean module syntax')
    imports = result.get('imports')
    if not isinstance(imports, list):
        raise ValueError('Lean header imports missing')
    modules = []
    for item in imports:
        if not isinstance(item, dict) or not isinstance(item.get('module'), str):
            raise ValueError('Malformed import entry')
        parts = item['module'].split('.')
        if not all(part.isidentifier() for part in parts):
            raise ValueError('Cannot safely map module name: ' + item['module'])
        modules.append(parts)
    return modules


def project_local_imports(header, project, source_roots=()):
    root = Path(project).resolve(strict=True)
    if not root.is_dir():
        raise ValueError('Project root is not a directory')
    roots = [root]
    for source in source_roots:
        source = Path(source)
        candidate = source if source.is_absolute() else root / source
        resolved = candidate.resolve(strict=True)
        if not resolved.is_relative_to(root) or not resolved.is_dir():
            raise ValueError('Source root must be a directory inside the project')
        roots.append(resolved)
    found = []
    for parts in direct_imports(header):
        for source in roots:
            candidate = source
            for component in (*parts[:-1], parts[-1] + '.lean'):
                candidate = candidate / component
                if candidate.is_symlink():
                    raise ValueError('Symlink in project import path: ' + '.'.join(parts))
            if candidate.exists():
                if not candidate.is_file():
                    raise ValueError('Project import is not a regular file: ' + '.'.join(parts))
                found.append('.'.join(parts))
    return sorted(set(found))


def check(lean, challenge, project, source_roots=()):
    root = Path(project).resolve(strict=True)
    path = Path(challenge).resolve(strict=True)
    if not path.is_relative_to(root) or not path.is_file():
        raise ValueError('Challenge must be a file under the project root')
    run = subprocess.run([str(lean), '--deps-json', str(path)], check=True,
                         capture_output=True, text=True, timeout=30)
    header = json.loads(run.stdout)
    local = project_local_imports(header, root, source_roots)
    return {'project_local_direct_imports': local,
            'scope': 'Direct imports under supplied project source roots only; protected compile and transitive provenance audit remain required.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--challenge', required=True)
    parser.add_argument('--project-root', required=True)
    parser.add_argument('--source-root', action='append', default=[],
                        help='Additional project-relative or absolute source root; repeat for each non-default root.')
    args = parser.parse_args()
    result = check(args.lean, args.challenge, args.project_root, args.source_root)
    print(json.dumps(result, indent=2))
    return 1 if result['project_local_direct_imports'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
