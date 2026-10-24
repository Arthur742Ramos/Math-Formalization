import argparse,hashlib,json,pathlib,subprocess
p=pathlib.Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--lean-prefix',type=pathlib.Path);a=parser.parse_args()
d=json.loads((p/'verification/core-definitions.json').read_text());doc=(p/'CORE-DEFINITIONS.md').read_text();sha=lambda b:hashlib.sha256(b).hexdigest()
assert d['compiler_commit']=='11acb17ec6b07a8f9e9173e6845197929540936b'
assert d['source_url']=='https://github.com/leanprover/lean4/blob/'+d['compiler_commit']+'/src/'+d['source_path']
assert d['source_url']in doc and d['sha256']in doc and d['upstream_header']in doc
for x in d['excerpts']:assert sha(x['text'].encode())==x['sha256'] and x['text']in doc
if a.lean_prefix:
 raw=(a.lean_prefix/'src/lean'/d['source_path']).read_bytes();assert sha(raw)==d['sha256'] and raw.startswith(d['upstream_header'].encode())
 for x in d['excerpts']:assert b''.join(raw.splitlines(keepends=True)[x['first_line']-1:x['last_line']])==x['text'].encode()
 assert d['compiler_commit']in subprocess.check_output([str(a.lean_prefix/'bin/lean'),'--version'],text=True)
for extra in d.get('additional_sources',[]):
 assert extra['source_url']=='https://github.com/leanprover/lean4/blob/'+d['compiler_commit']+'/src/'+extra['source_path']
 assert extra['source_url'] in doc and extra['sha256'] in doc and extra['upstream_header'] in doc
 for x in extra['excerpts']:assert sha(x['text'].encode())==x['sha256'] and x['text'] in doc
 if a.lean_prefix:
  raw=(a.lean_prefix/'src/lean'/extra['source_path']).read_bytes();assert sha(raw)==extra['sha256'] and raw.startswith(extra['upstream_header'].encode())
  for x in extra['excerpts']:assert b''.join(raw.splitlines(keepends=True)[x['first_line']-1:x['last_line']])==x['text'].encode()
print(json.dumps({'status':'pass','compiler_commit':d['compiler_commit'],'source_sha256':d['sha256'],'excerpts':[x['name']for x in d['excerpts']],'installed_source_authenticated':bool(a.lean_prefix),'scope':'Retained core data consistency and exact installed compiler-source binding; semantic bridges and independent fidelity review are separate.'}))
