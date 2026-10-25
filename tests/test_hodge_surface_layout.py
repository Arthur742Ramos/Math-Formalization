"""Layout regression tests: complete proofs and lexical comments must survive."""
import ast
import pathlib
import re
import unittest

ROOT=pathlib.Path(__file__).resolve().parents[1]
SOURCE=ROOT/'computational-hodge/automatic-lifts/scripts/make_surface.py'
tree=ast.parse(SOURCE.read_text())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='compact_complete_source')
namespace={'re':re}
exec(compile(ast.Module(body=[function],type_ignores=[]),str(SOURCE),'exec'),namespace)
compact=namespace['compact_complete_source']

class CompleteSurfaceLayout(unittest.TestCase):
    def test_ordinary_signature_only(self):
        src='theorem demo\n    (x : Nat) : x=x := by\n  rfl\n'
        out,meta=compact(src)
        self.assertEqual(out,'theorem demo (x : Nat) : x=x := by\n  rfl\n')
        self.assertEqual(meta['ordinary_signature_line_joins'],1)
        self.assertEqual(meta['proof_body_line_joins'],0)

    def test_header_line_comment_cannot_swallow_type(self):
        src='theorem demo -- keep this comment\n    : True := by\n  trivial\n'
        self.assertEqual(compact(src)[0],src)

    def test_continuation_line_comment_is_not_joined(self):
        src='theorem demo\n    (x : Nat) -- keep next line live\n    : x=x := by\n  rfl\n'
        self.assertEqual(compact(src)[0],src)

    def test_nested_block_comments_and_blank_lines_preserved(self):
        src='/- outer\n\n /- inner -/\n\n-/\n\ntheorem demo : True := by\n  trivial\n'
        self.assertEqual(compact(src)[0],src.replace('-/\n\ntheorem','-/\ntheorem'))

    def test_multiline_string_blank_lines_preserved(self):
        src='def text := "first\n\nlast"\n'
        self.assertEqual(compact(src)[0],src)

    def test_escaped_quote_and_comment_text_in_string(self):
        src='def text := "a \\" quote -- text"\n\ntheorem demo : True := by\n  trivial\n'
        self.assertEqual(compact(src)[0],src.replace('"\n\ntheorem','"\ntheorem'))

    def test_proof_and_open_commands_never_joined(self):
        src='open A\nopen B\ntheorem demo : True := by\n  have h : True := by\n    trivial\n  exact h\n'
        self.assertEqual(compact(src)[0],src)

if __name__=='__main__':unittest.main()
