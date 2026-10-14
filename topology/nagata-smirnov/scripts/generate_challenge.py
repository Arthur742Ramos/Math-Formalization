"""Build the independent canonical-import Challenge from the reviewed sources."""
import pathlib,re
root=pathlib.Path(__file__).resolve().parents[1]
names=['SigmaBasis','CompatibleMetric','MetricBasis','Metrization']
imports=[]
bodies=[]
for name in names:
    text=(root/(name+'.lean')).read_text(encoding='utf-8')
    for item in re.findall(r'^public import (\S+)$',text,re.M):
        if item.startswith('Mathlib.') and item not in imports: imports.append(item)
    body=text[text.index('/-!',text.index('module')):]
    body=re.sub(r'^(?:@\[expose\] )?public section\s*\n','',body,flags=re.M)
    bodies.append(body)
header='''/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

'''
challenge=header+'\n'.join('public import '+x for x in imports)+'\n\n@[expose] public section\n\n'+'\n'.join(bodies)
(root/'Challenge.lean').write_text(challenge,encoding='utf-8',newline='\n')
print({'challenge_lines':len(challenge.splitlines()),'challenge_bytes':len(challenge.encode())})
