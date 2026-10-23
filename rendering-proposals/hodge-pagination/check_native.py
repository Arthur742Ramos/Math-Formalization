"""Check a diagnostic pagination artifact; never emits canonical acceptance."""
from html.parser import HTMLParser
from pathlib import Path
import hashlib
import json
import sys
from urllib.parse import urlsplit, unquote


class View(HTMLParser):
    def __init__(self):
        super().__init__()
        self.blocks = []; self.current = None; self.code_depth = 0
        self.ids = set(); self.hrefs = []; self.definitions = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get('id'): self.ids.add(attrs['id'])
        if attrs.get('href'): self.hrefs.append(attrs['href'])
        if attrs.get('id') and attrs.get('data-binding', '').startswith('const-'):
            self.definitions.append(attrs['data-binding'][6:])
        if tag == 'code':
            if self.current is not None: self.code_depth += 1
            elif set(['hl', 'lean', 'block']).issubset(attrs.get('class', '').split()):
                self.current = []; self.code_depth = 1

    def handle_endtag(self, tag):
        if tag == 'code' and self.current is not None:
            self.code_depth -= 1
            if self.code_depth == 0:
                self.blocks.append(''.join(self.current)); self.current = None

    def handle_data(self, text):
        if self.current is not None: self.current.append(text)


def view(path):
    p = View(); p.feed(path.read_text()); p.close(); return p


def check(baseline_html, raw, sanitized, comparator):
    metadata = json.loads((raw / 'HodgeChallenge/source-pages.json').read_text())
    pages = [raw / 'HodgeChallenge' / name for name in metadata['pages']]
    baseline = view(baseline_html)
    source_blocks = [b for p in pages for b in view(p).blocks]
    if source_blocks != baseline.blocks:
        raise ValueError('Source command/proof-state text differs or is missing/reordered')
    config = json.loads(comparator.read_text())
    selected = config['theorem_names'] + config['definition_names']
    entry = view(sanitized / 'Challenge/index.html')
    if any(entry.definitions.count(name) != 1 for name in selected):
        raise ValueError('Selected declaration missing or duplicated')
    parsed = {p.relative_to(sanitized).as_posix(): view(p) for p in sanitized.rglob('*.html')}
    broken = []
    for name, p in parsed.items():
        for href in p.hrefs:
            url = urlsplit(href)
            if url.scheme or url.netloc: continue
            if url.path.startswith('../HodgeChallenge/') or url.path.startswith('../Challenge/'):
                target = url.path[3:]
                if target.endswith('/'): target += 'index.html'
                if target not in parsed or (url.fragment and unquote(url.fragment) not in parsed[target].ids):
                    broken.append({'page': name, 'href': href})
    if broken: raise ValueError('Broken internal Hodge routes: ' + repr(broken[:5]))
    return {'scope': 'Native diagnostic only, not canonical run or browser acceptance',
            'source_code_blocks_in_original_order': len(source_blocks),
            'source_code_and_proof_state_text': 'exactly equal to original baseline blocks',
            'selected_declarations_exactly_once': len(selected),
            'source_pages': len(pages), 'checked_internal_hodge_links': 'all valid',
            'baseline_html_sha256': hashlib.sha256(baseline_html.read_bytes()).hexdigest()}


if __name__ == '__main__':
    if len(sys.argv) != 5: raise SystemExit('BASELINE_HTML RAW_PAGES SANITIZED COMPARATOR')
    print(json.dumps(check(*(Path(p) for p in sys.argv[1:])), indent=2))
