#!/usr/bin/env python3
"""Source/provenance consistency only; mathematical and kernel checks are separate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess

root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--upstream-root',type=Path)
args=parser.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run(['python3',str(root/'scripts/make_surface.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
provenance=json.loads((root/'source-provenance.json').read_text())
source=(root/'SourcePaths.lean').read_text()
authenticated=0
for row in provenance['excerpts']:
    if args.upstream_root:
        base=args.upstream_root
        git=lambda *xs:subprocess.check_output(['git','-C',str(base),*xs])
        assert git('rev-parse','HEAD').decode().strip()==provenance['upstream_commit']
        raw=git('show',provenance['upstream_commit']+':'+row['path'])
        assert raw==(base/row['path']).read_bytes() and sha(raw)==row['source_sha256']
        text=raw.decode();begin=text.index(row['start_marker']);end=text.index(row['end_marker'])
        excerpt=text[begin:end].rstrip()+'\n'
        assert sha(excerpt.encode())==row['excerpt_sha256'] and excerpt in source
        chunk=excerpt+('\nend GeometricTrace\n' if row['namespace_closure_added'] else '')
        assert sha(chunk.encode())==row['port_chunk_sha256']
        assert text[:begin].count('\n')+1==row['first_line']
        assert row['last_line']==row['first_line']+len(excerpt.splitlines())-1
        authenticated+=1
    else:
        assert re.fullmatch('[0-9a-f]{64}',row['excerpt_sha256'])
assert len(provenance['excerpts'])==3 and provenance['upstream_commit']=='ea1367d99c7d2f3794f1299cce5b18379e9093a7'
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
packages=json.loads((root/'lake-manifest.json').read_text())['packages']
assert next(p for p in packages if p['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
config=json.loads((root/'comparator.json').read_text())
assert (len(config['theorem_names']),len(config['definition_names']))==(16,25)
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert config['challenge_module']=='Challenge' and config['solution_module']=='Solution'

def erase_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(text[i]);i+=1
    assert depth==0
    return ''.join(out)

for p in root.glob('*.lean'):
    text=erase_comments(p.read_text())
    assert text.lstrip().startswith('module'),p.name
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|set_option)\b',text),p.name
meta=json.loads((root/'formalization.yaml').read_text())
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert meta['status']['axioms']==config['permitted_axioms']
assert 'analytic' in meta['status']['known_gaps'] and 'all-basepoint' in meta['status']['scope']
subprocess.run(['python3',str(root.parents[1]/'scripts/check_imported_definitions.py'),
    '--project-path',str(root),'--dependency-root',str(root/'.lake/packages/mathlib')],check=True)
print(json.dumps(dict(status='pass',upstream_excerpt_files_authenticated=authenticated,
    source_scope='Consistency only; exact-source compilation, comparison, kernels and independent review remain separately evidenced.'),indent=2))
