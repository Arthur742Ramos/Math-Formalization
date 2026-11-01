"""Conservative scanner for the supported Lean module-header import syntax.

It is not Lean's parser and does not authenticate the transitive dependencies.
Unrecognized module identifiers and malformed comments fail closed.
"""
import re

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def skip_trivia(text, pos):
    while pos < len(text):
        if text[pos].isspace() or (pos == 0 and text[pos] == '\ufeff'):
            pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end + 1
        elif text.startswith('/-', pos):
            depth = 1
            pos += 2
            while depth and pos < len(text):
                if text.startswith('/-', pos):
                    depth += 1; pos += 2
                elif text.startswith('-/', pos):
                    depth -= 1; pos += 2
                else:
                    pos += 1
            if depth:
                raise ValueError('unterminated block comment in module header')
        else:
            break
    return pos


def token(text, pos):
    pos = skip_trivia(text, pos)
    match = IDENT.match(text, pos)
    return (match.group(), match.end()) if match else (None, pos)


def header_imports(text):
    word, pos = token(text, 0)
    if word != 'module':
        raise ValueError('expected module header')
    word, end = token(text, pos)
    if word == 'prelude':
        pos = end
    imports = []
    while True:
        start = pos
        word, pos = token(text, pos)
        public = word == 'public'
        if word == 'public':
            word, pos = token(text, pos)
        if word == 'meta':
            word, pos = token(text, pos)
        if word != 'import':
            pos = start
            break
        word, pos = token(text, pos)
        if word == 'all':
            if public:
                raise ValueError('Lean disallows public import all')
            word, pos = token(text, pos)
        if word is None:
            raise ValueError('missing or unsupported import module identifier')
        # Reject truncated dotted or escaped identifiers rather than accepting a prefix.
        if pos < len(text) and (text[pos] in '.«»' or text[pos].isalnum() or text[pos] in "_'"):
            raise ValueError('unsupported import module identifier')
        imports.append(word)
    return imports
