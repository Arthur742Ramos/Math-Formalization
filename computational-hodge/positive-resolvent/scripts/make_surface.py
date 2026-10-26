#!/usr/bin/env python3
"""Preserve all retained declarations/proofs; remove only witnessed redundant trusted imports."""
from pathlib import Path
import argparse,hashlib,json,re

root=Path(__file__).resolve().parents[1]
modules=['SourcePaths', 'Periods', 'Harmonic', 'LoopImage', 'CircleWinding', 'CircleData', 'RawLift', 'CirclePeriods', 'ACAnalysis', 'ACPeriods', 'Potential', 'Density', 'Poisson', 'Green', 'CompactGreen', 'Fredholm', 'FullOperator', 'Positive']
documentation_header_placement=[]
def place_documentation_headers(text):
    """After ordinary signature layout, preserve each docstring with its declaration."""
    matches=list(re.finditer(r'(?m)^/--(?:(?!/\-).)*?-/\n',text,re.S))
    output=[];pos=0
    for match in matches:
        stack=[]
        for line in text[:match.start()].splitlines():
            if line.startswith('namespace '):stack.append(line.split()[1])
            elif line.startswith('end '):
                assert stack and stack[-1]==line.split()[1];stack.pop()
        if not stack or not '.'.join(stack).startswith('ComputationalHodge'):continue
        original=match[0];prose=original[3:original.rfind('-/')]
        assert not any(word in prose for word in ['@[','set_option','/-','\n#']), 'Nonplain documentation requires separate review'
        declaration=re.match(r'(?:noncomputable )?(?:theorem|def|abbrev|instance|structure) ([A-Za-z_][A-Za-z_0-9]*)',text[match.end():]);assert declaration,original
        normalized=' '.join(prose.split());assert normalized.split()==prose.split()
        replacement='/-- '+normalized+' -/ '
        documentation_header_placement.append(dict(declaration='.'.join(stack+[declaration[1]]),original_docstring=original,original_sha256=hashlib.sha256(original.encode()).hexdigest(),prose=normalized,replacement=replacement,start_character=match.start(),end_character=match.end(),association='Per-declaration Lean docstring association retained; modular docstrings unchanged.'))
        output.extend([text[pos:match.start()],replacement]);pos=match.end()
    output.append(text[pos:]);result=''.join(output)
    strip=lambda value:re.sub(r'(?m)^/--(?:(?!/\-).)*?-/(?:\n|[ \t]+)','',value,flags=re.S)
    assert strip(result)==strip(text),'Statement/proof/context bytes changed by documentation placement'
    assert len(documentation_header_placement)==44
    return result

imports=[];chunks=[];sources=[]
for module in modules:
    path=root/(module+'.lean');raw=path.read_bytes();text=raw.decode()
    sources.append(dict(path=path.name,sha256=hashlib.sha256(raw).hexdigest()))
    lines=[]
    for line in text.splitlines():
        match=re.fullmatch(r'public import (\S+)',line)
        if match:
            name=match[1]
            if name.startswith('Mathlib.') and name not in imports: imports.append(name)
        elif line not in ['module','@[expose] public section']:
            lines.append(line)
    chunks.append('\n'.join(lines).strip())
import_record=json.loads((root/'import-provenance.json').read_text())
assert imports==import_record['original_imports']
imports=import_record['retained_imports']
body='module\n\n'+'\n'.join('public import '+x for x in imports)
body+='\n/-! Complete retained proofs and documented exact adaptations. -/\n'
body+='@[expose] public section\n\n'+'\n\n'.join(chunks)+'\n'
# Embedded verbatim in make_surface.py. Mathematical proof bodies are not joined.
def compact_complete_source(text):
    lines=text.splitlines();output=[];depth=0;quoted=False;index=0;removed=0;joined=0
    def state_after(line,depth,quoted):
        i=0;line_comment=False
        while i<len(line):
            if depth:
                if line.startswith('/-',i):depth+=1;i+=2
                elif line.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            elif quoted:
                if ord(line[i])==92:i+=2
                elif line[i]=='"':quoted=False;i+=1
                else:i+=1
            elif line.startswith('--',i):line_comment=True;break
            elif line.startswith('/-',i):depth+=1;i+=2
            elif line[i]=='"':quoted=True;i+=1
            else:i+=1
        return depth,quoted,line_comment
    while index<len(lines):
        line=lines[index];index+=1
        if not line.strip()and depth==0 and not quoted:
            removed+=1;continue
        at_code=depth==0 and not quoted
        depth,quoted,line_comment=state_after(line,depth,quoted)
        if at_code and re.match(r'^(?:noncomputable )?(?:theorem|def|abbrev|structure)\b',line):
            while ':='not in line and not re.search(r'\bwhere\b',line)and depth==0 and not quoted and not line_comment and index<len(lines)and lines[index].startswith(' ')and not lines[index].lstrip().startswith(('|','/-','--')):
                continuation=lines[index]
                next_depth,next_quoted,next_comment=state_after(continuation,depth,quoted)
                if next_comment or next_depth or next_quoted:break
                index+=1;line+=' '+continuation.strip();joined+=1
                depth,quoted,line_comment=next_depth,next_quoted,next_comment
        output.append(line)
    assert depth==0 and not quoted
    return '\n'.join(output)+'\n',dict(empty_code_lines_removed=removed,ordinary_signature_line_joins=joined,proof_body_line_joins=0,open_command_joins=0)

unformatted_sha256=hashlib.sha256(body.encode()).hexdigest()
body,layout=compact_complete_source(body)
body=place_documentation_headers(body)
layout['documentation_header_joins']=len(documentation_header_placement)
data=body.encode();assert len(data)<=100*1024 and len(body.splitlines())<=1000
manifest=dict(schema_version=4,documentation_header_placement=documentation_header_placement,unformatted_sha256=unformatted_sha256,layout=layout,ordered_sources=sources,mathlib_imports=imports,
    sha256=hashlib.sha256(data).hexdigest(),lines=len(body.splitlines()),bytes=len(data),
    transformation='Remove module/visibility directives; replace custom imports by complete source and minimize only witnessed redundant trusted Mathlib imports; remove empty lines outside comments/strings and reflow ordinary top-level declaration signatures and preserve plain docstring prose with its original declaration through header placement after ordinary signature layout. Modular docstrings stay unchanged; combined per-declaration Lean doc metadata is retained. No proof-body or open-command joins. Retain every declaration and complete proof of ordered modular sources; fresh elaboration and review remain required. Challenge and Solution share one implementation, not independent proofs.')
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
for name in ['Challenge.lean','Solution.lean']:
    target=root/name
    if args.check: assert target.read_bytes()==data, name+' is stale'
    else: target.write_bytes(data)
target=root/'surface-manifest.json';encoded=(json.dumps(manifest,indent=2)+'\n').encode()
if args.check: assert target.read_bytes()==encoded,'surface manifest is stale'
else: target.write_bytes(encoded)
print(json.dumps(manifest,indent=2))
