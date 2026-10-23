"""Inert native pagination prototype; NOT the Palomar canonical renderer.

Call only on whole-command output from the paired Verso proposal. This does
not lift any limit, execute a browser, or emit a canonical acceptance report.
"""
from html.parser import HTMLParser
from pathlib import Path
import argparse
import html
import json
import shutil


class Anchors(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids = set()
        self.content_depth = None
        self.depth = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'section' and 'code-content' in attrs.get('class', '').split():
            self.content_depth = self.depth
        if self.content_depth is not None and attrs.get('id'):
            self.ids.add(attrs['id'])
        if tag not in {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}:
            self.depth += 1

    def handle_endtag(self, tag):
        self.depth -= 1
        if self.content_depth is not None and self.depth <= self.content_depth:
            self.content_depth = None


def route_url(value, module_path, owners):
    if value in (module_path + "/", module_path + "/index.html"):
        return "Challenge/index.html"
    if value in ("/" + module_path + "/", "/" + module_path + "/index.html"):
        return "/Challenge/index.html"
    for prefix in (module_path + '/#', '/' + module_path + '/#',
                   module_path + '/index.html#', '/' + module_path + '/index.html#'):
        if value.startswith(prefix):
            anchor = value[len(prefix):]
            if anchor in owners:
                return ('/' if prefix.startswith('/') else '') + owners[anchor] + '#' + anchor
    if value.startswith('#') and value[1:] in owners:
        return owners[value[1:]] + value
    return value


class RouteHTML(HTMLParser):
    def __init__(self, module_path, owners, navigation=''):
        super().__init__(convert_charrefs=False)
        self.module_path, self.owners = module_path, owners
        self.parts = []
        self.navigation = navigation
        self.insertions = 0

    def handle_starttag(self, tag, attrs):
        rewritten = [(k, route_url(v, self.module_path, self.owners)
                      if k == 'href' and v is not None else v) for k, v in attrs]
        if attrs == rewritten:
            self.parts.append(self.get_starttag_text())
        else:
            self.parts.append('<' + tag + ''.join(
                ' ' + k if v is None else ' ' + k + '="' + html.escape(v, quote=True) + '"'
                for k, v in rewritten) + '>')
        if tag == 'section' and 'code-content' in dict(attrs).get('class', '').split():
            self.parts.append(self.navigation)
            self.insertions += 1

    def handle_startendtag(self, tag, attrs):
        # Upstream emits void tags here; route handling is identical, apart
        # from preserving its self-closing form when nothing changed.
        before = len(self.parts)
        self.handle_starttag(tag, attrs)
        if self.parts[before] == self.get_starttag_text():
            return
        self.parts[before] = self.parts[before][:-1] + ' />'

    def handle_endtag(self, tag): self.parts.append('</' + tag + '>')
    def handle_data(self, data): self.parts.append(data)
    def handle_entityref(self, name): self.parts.append('&' + name + ';')
    def handle_charref(self, name): self.parts.append('&#' + name + ';')
    def handle_comment(self, data): self.parts.append('<!--' + data + '-->')
    def handle_decl(self, data): self.parts.append('<!' + data + '>')


def route_html(text, module_path, owners, navigation=''):
    parser = RouteHTML(module_path, owners, navigation)
    parser.feed(text)
    parser.close()
    if parser.rawdata or (navigation and parser.insertions != 1):
        raise ValueError('Incomplete HTML or ambiguous source section')
    return ''.join(parser.parts)


def route_json(value, module_path, owners):
    if isinstance(value, dict):
        result = {}
        for k, v in value.items():
            key = route_url(k, module_path, owners)
            if key in result:
                raise ValueError('Routing collides JSON keys')
            result[key] = route_json(v, module_path, owners)
        # Verso xref domain entries encode address and anchor separately.
        if value.get('address') in ('/' + module_path + '/', module_path + '/') and value.get('id') in owners:
            result['address'] = ('/' if value['address'].startswith('/') else '') + owners[value['id']]
        return result
    if isinstance(value, list):
        return [route_json(v, module_path, owners) for v in value]
    if isinstance(value, str):
        if '<' in value and 'href=' in value:
            return route_html(value, module_path, owners)
        return route_url(value, module_path, owners)
    return value


def prepare(input_dir, output_dir, module):
    if module != "HodgeChallenge":
        raise ValueError("This prototype is restricted to the Hodge module")
    if not input_dir.is_dir() or input_dir.is_symlink() or output_dir.exists():
        raise ValueError('Use a real input and a new output directory')
    if any(path.is_symlink() for path in input_dir.rglob("*")):
        raise ValueError("Symlink output")
    module_path = module.replace('.', '/')
    root = input_dir / module_path
    metadata = json.loads((root / 'source-pages.json').read_text())
    names = metadata['pages']
    if metadata['module'] != module or not names or len(names) != len(set(names)):
        raise ValueError('Wrong module or duplicate/empty page list')
    if any(n != f'source-{i + 1}.html' for i, n in enumerate(names)):
        raise ValueError('Noncanonical page path')
    owners = {}
    for name in names:
        parser = Anchors(); parser.feed((root / name).read_text())
        for anchor in parser.ids - {module}:
            if anchor in owners:
                raise ValueError('Duplicate source anchor: ' + anchor)
            owners[anchor] = module_path + '/' + name
    links = ''.join('<a href="' + module_path + '/' + name + '">Source page ' + str(i + 1) + '</a> '
                    for i, name in enumerate(names))
    navigation = '<nav class="palomar-source-navigation" aria-label="Complete source">' + links + '</nav>'
    # Check exactly the same raw file/total bounds before AND after routing.
    def bounds(directory):
        paths = list(directory.rglob('*'))
        if len(paths) > 4000: raise ValueError('Node cap exceeded')
        total = files = 0
        for path in paths:
            if path.is_symlink(): raise ValueError('Symlink output')
            if path.is_dir(): continue
            if not path.is_file(): raise ValueError('Nonregular output')
            size = path.stat().st_size
            if size > 8 * 1024 * 1024: raise ValueError('File cap exceeded')
            total += size; files += 1
        if total > 25 * 1024 * 1024 or files > 2000: raise ValueError('Artifact cap exceeded')
    bounds(input_dir)
    shutil.copytree(input_dir, output_dir)
    for path in output_dir.rglob('*'):
        if path.suffix == '.html':
            nav = navigation if path.parent == output_dir / module_path else ''
            path.write_text(route_html(path.read_text(), module_path, owners, nav))
        elif path.suffix == '.json':
            path.write_text(json.dumps(route_json(json.loads(path.read_text()), module_path, owners),
                                       ensure_ascii=False, separators=(',', ':')))
    bounds(output_dir)
    return {'scope': 'local prototype only; no canonical verdict', 'module': module,
            'source_pages': len(names), 'routed_source_anchors': len(owners),
            'search_javascript': 'not rewritten; canonical sanitizer discards input JS; do not claim raw Verso search support',
            'browser_navigation': 'requires paired inert runtime patch, not current canonical runtime'}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input_dir', type=Path); p.add_argument('output_dir', type=Path)
    p.add_argument('--module', required=True)
    a = p.parse_args()
    print(json.dumps(prepare(a.input_dir, a.output_dir, a.module), indent=2))
