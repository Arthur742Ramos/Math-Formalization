#!/usr/bin/env python3
"""Preserve every declaration and complete proof from the eight ordered modules."""
from pathlib import Path
import argparse,hashlib,json,re

root=Path(__file__).resolve().parents[1]
modules=['SourcePaths', 'Periods', 'Harmonic', 'LoopImage', 'Characters', 'Reconstruction', 'HarmonicCharacters', 'CharacterExample']
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
body='module\n\n'+'\n'.join('public import '+x for x in imports)
body+='\n\n/-! Proof-complete shared generated source. All retained declarations and proofs\n'
body+='are copied verbatim from the ordered modular sources. No source pruning.\n'
body+='The upstream MIT attribution and SOURCE-LICENSE.txt remain applicable. -/\n\n'
body+='@[expose] public section\n\n'+'\n\n'.join(chunks)+'\n'
data=body.encode();assert len(data)<=100*1024 and len(body.splitlines())<=1000
manifest=dict(schema_version=1,ordered_sources=sources,mathlib_imports=imports,
    sha256=hashlib.sha256(data).hexdigest(),lines=len(body.splitlines()),bytes=len(data),
    transformation='Remove module/public-import/public-section directives only; copy every other source line and complete proof in source order. Challenge and Solution share one implementation, not independent proofs.')
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
for name in ['Challenge.lean','Solution.lean']:
    target=root/name
    if args.check: assert target.read_bytes()==data, name+' is stale'
    else: target.write_bytes(data)
target=root/'surface-manifest.json';encoded=(json.dumps(manifest,indent=2)+'\n').encode()
if args.check: assert target.read_bytes()==encoded,'surface manifest is stale'
else: target.write_bytes(encoded)
print(json.dumps(manifest,indent=2))
