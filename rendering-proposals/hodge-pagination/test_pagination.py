"""Native/local regression checks; no canonical or browser acceptance."""
from pathlib import Path
from html.parser import HTMLParser
import importlib.util
import json
import sys
import tempfile
import unittest

P = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('routes', P / 'route_pages.py')
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)


class Routes(unittest.TestCase):
    def setUp(self):
        self.owners = {'a': 'HodgeChallenge/source-2.html'}

    def test_definition_fragment_and_entrypoint_routes(self):
        self.assertEqual(r.route_url('HodgeChallenge/#a', 'HodgeChallenge', self.owners),
                         'HodgeChallenge/source-2.html#a')
        self.assertEqual(r.route_url('HodgeChallenge/', 'HodgeChallenge', self.owners),
                         'Challenge/index.html')
        self.assertEqual(r.route_url('#a', 'HodgeChallenge', self.owners),
                         'HodgeChallenge/source-2.html#a')

    def test_unrelated_urls_and_source_text_are_preserved(self):
        for value in ['#main-content', 'https://example.org/#a', 'Other/#a']:
            self.assertEqual(r.route_url(value, 'HodgeChallenge', self.owners), value)
        text = '<code>literal href=&quot;HodgeChallenge/#a&quot;</code>'
        self.assertEqual(r.route_html(text, 'HodgeChallenge', self.owners), text)

    def test_attribute_escaping_cannot_become_markup(self):
        source = '<a title="x href=&quot;HodgeChallenge/#a&quot;" href="HodgeChallenge/#a">x</a>'
        output = r.route_html(source, 'HodgeChallenge', self.owners)
        self.assertIn('title="x href=&quot;HodgeChallenge/#a&quot;"', output)
        self.assertIn('href="HodgeChallenge/source-2.html#a"', output)
        self.assertEqual(output.count('<a '), 1)

    def test_xref_split_address_and_docstring_html(self):
        value = {'address': '/HodgeChallenge/', 'id': 'a',
                 'doc': '<a href="HodgeChallenge/#a">a</a>'}
        routed = r.route_json(value, 'HodgeChallenge', self.owners)
        self.assertEqual(routed['address'], '/HodgeChallenge/source-2.html')
        self.assertIn('source-2.html#a', routed['doc'])

    def test_colliding_json_routes_rejected(self):
        with self.assertRaises(ValueError):
            r.route_json({"HodgeChallenge/#a": 1, "HodgeChallenge/source-2.html#a": 2},
                         "HodgeChallenge", self.owners)

    def test_ambiguous_navigation_section_rejected(self):
        with self.assertRaises(ValueError):
            r.route_html('<body>x</body>', 'HodgeChallenge', self.owners, '<nav>x</nav>')

    def test_duplicate_page_path_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t) / 'in'; (root / 'HodgeChallenge').mkdir(parents=True)
            (root / 'HodgeChallenge/source-pages.json').write_text(json.dumps(
                {'module': 'HodgeChallenge', 'pages': ['source-1.html', 'source-1.html']}))
            with self.assertRaises(ValueError): r.prepare(root, Path(t) / 'out', 'HodgeChallenge')

    def test_wrong_module_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t) / 'in'; (root / 'HodgeChallenge').mkdir(parents=True)
            (root / 'HodgeChallenge/source-pages.json').write_text(json.dumps(
                {'module': 'Other', 'pages': ['source-1.html']}))
            with self.assertRaises(ValueError): r.prepare(root, Path(t) / 'out', 'HodgeChallenge')

    def test_input_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t) / 'in'; root.mkdir(); (Path(t) / 'alias').symlink_to(root)
            with self.assertRaises(ValueError): r.prepare(Path(t) / 'alias', Path(t) / 'out', 'HodgeChallenge')


if __name__ == '__main__': unittest.main()
