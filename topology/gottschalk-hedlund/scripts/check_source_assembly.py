"""Check the self-contained Challenge against the retained source fragments."""
import hashlib,json
from pathlib import Path

P=Path(__file__).resolve().parents[1]
ORDER=['CocycleDevelopment','MinimalInvariantDevelopment','CompactSkewDevelopment','VerticalFiberDevelopment','MinimalSkewFibers','ProjectionGraphDevelopment','GottschalkHedlundDevelopment']
manifest=json.loads((P/'SOURCE-MANIFEST.json').read_text(encoding='utf-8'))
if set(manifest['source_sha256'])!=set(ORDER):raise SystemExit('Unexpected source fragment set')
imports=[];sections=[]
for name in ORDER:
 data=(P/'sources'/(name+'.lean.txt')).read_bytes()
 if hashlib.sha256(data).hexdigest()!=manifest['source_sha256'][name]:raise SystemExit('Fragment hash mismatch: '+name)
 body=[]
 for line in data.decode('utf-8').splitlines():
  if line.startswith('import '):
   module=line.removeprefix('import ').strip()
   if module.startswith('Mathlib.'):
    if module not in imports:imports.append(module)
   elif module not in ORDER:raise SystemExit('Unexpected local import: '+module)
  else:body.append(line)
 sections.append('\n'.join(body).strip()+'\n')
header='/-\nScalar Gottschalk–Hedlund theorem. Apache-2.0; see ATTRIBUTION.md.\nMaterial Lean proof developed by OpenAI Codex.\n-/\nmodule\n'+''.join('public import '+x+'\n' for x in imports)+'\n@[expose] public section\n\n'
body=header+'\n'.join(sections)
change=manifest['comment_transformation']
if change.get('from')!='This module provides supporting lemmas; the existence proof is in the final development module.' or change.get('to')!='These sections provide supporting lemmas and the existence proof.':raise SystemExit('Unexpected comment transformation')
if body.count(change['from'])!=1:raise SystemExit('Comment transformation source mismatch')
expected=body.replace(change['from'],change['to']).encode('utf-8')
if hashlib.sha256(expected).hexdigest()!=manifest['generated_sha256']:raise SystemExit('Generated source digest mismatch')
for name in ('GottschalkHedlund.lean','GHChallenge.lean'):
 if (P/name).read_bytes()!=expected:raise SystemExit('Source differs: '+name)
print('Challenge and core match retained source fragments; compilation and protected verification are separate.')