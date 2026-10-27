#!/usr/bin/env python3
"""Generate complete selected-source surfaces without hiding proof bodies."""
from pathlib import Path
import argparse,hashlib,json,re
root=Path(__file__).resolve().parents[1]
modules=['SourcePaths', 'Periods', 'Harmonic', 'LoopImage', 'CircleWinding', 'CircleData', 'RawLift', 'CirclePeriods', 'ACAnalysis', 'ACPeriods', 'Potential', 'Density', 'Poisson', 'Green', 'Fredholm', 'Resonance', 'ArclengthCoordinate', 'CoordinateRegularity', 'Conjugacy', 'TracePhase', 'FourierModes', 'GeometricModes', 'GeometricPathModes', 'FrequencyConsequences']
imports=[];chunks=[];sources=[]
for module in modules:
    path=root/(module+'.lean');raw=path.read_bytes();text=raw.decode();sources.append(dict(path=path.name,sha256=hashlib.sha256(raw).hexdigest()))
    lines=[]
    for line in text.splitlines():
        match=re.fullmatch(r'public import (\S+)',line)
        if match:
            name=match[1]
            if name.startswith('Mathlib.') and name not in imports:imports.append(name)
        elif line not in ['module','@[expose] public section']:
            lines.append(line)
    chunks.append('\n'.join(lines).strip())
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

body='module\n\n'+'\n'.join('public import '+x for x in imports)+'\n@[expose] public section\n\n'+'\n\n'.join(chunks)+'\n'
unformatted=hashlib.sha256(body.encode()).hexdigest();body,layout=compact_complete_source(body);data=body.encode()
assert len(body.splitlines())<=1000 and len(data)<=100*1024
manifest=dict(schema_version=2,unformatted_sha256=unformatted,layout=layout,ordered_sources=sources,mathlib_imports=imports,sha256=hashlib.sha256(data).hexdigest(),lines=len(body.splitlines()),bytes=len(data),transformation='Retain complete selected modular declarations and proofs. Remove only module/import/visibility wrappers, empty code lines, and reflow ordinary top-level signatures; no proof-body or open-command joins. Challenge and Solution share this implementation.')
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
for name in ['Challenge.lean','Solution.lean']:
    target=root/name
    if args.check:assert target.read_bytes()==data, name+' is stale'
    else:target.write_bytes(data)
target=root/'surface-manifest.json';encoded=(json.dumps(manifest,indent=2)+'\n').encode()
if args.check:assert target.read_bytes()==encoded,'surface manifest is stale'
else:target.write_bytes(encoded)
print(json.dumps(manifest,indent=2))
