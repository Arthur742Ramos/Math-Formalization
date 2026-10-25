#!/usr/bin/env python3
"""Source/provenance consistency only; compilation, kernels and review are separate."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess
root=Path(__file__).resolve().parents[1]
repository=root.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--upstream-root',type=Path)
args=parser.parse_args()
sha=lambda body:hashlib.sha256(body).hexdigest()
git=lambda *xs:subprocess.check_output(['git','-C',str(repository),*xs])
subprocess.run(['python3',str(root/'scripts/make_surface.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
base=json.loads((root/'base-provenance.json').read_text())
assert base['base_tested_commit']=='4e31c311d97be4e2eb8c8fe6b8f5ec1ffc3c2956'
assert base['base_package_tree']=='89a43c37af58cb96424b8cc3cae079d91b0954ff'
assert {row['file'] for row in base['files']}=={'SourcePaths.lean','Periods.lean','Harmonic.lean','Chains.lean','Homology.lean','Duality.lean','Examples.lean'}
for row in base['files']:
    assert row['source_commit']==base['base_tested_commit']
    assert row['source_path']=='computational-hodge/presentation-homology/'+row['file']
    assert row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+row['source_commit']+'/'+row['source_path']
    raw=git('show',row['source_commit']+':'+row['source_path']);text=raw.decode()
    assert sha(raw)==row['source_file_sha256']
    chunks=[]
    for part in row['retained_slices']:
        chunk=text[part['start_char']:part['end_char_exclusive']]
        assert sha(chunk.encode())==part['sha256']
        assert text[:part['start_char']].count('\n')+1==part['start_line']
        assert text[:part['end_char_exclusive']].count('\n')+1==part['end_line_exclusive']
        chunks.append(chunk)
    retained=''.join(chunks)+row['appended_namespace_closure']
    for edit in row['import_rewrites']:
        assert retained.count(edit['old'])==1
        retained=retained.replace(edit['old'],edit['new'])
    for adaptation in row['proof_adaptations']:
        original=adaptation['original_declaration'];adapted=adaptation['adapted_declaration']
        assert retained.count(original)==1
        assert sha(original.encode())==adaptation['original_sha256']
        assert sha(adapted.encode())==adaptation['adapted_sha256']
        statement=original.split(':= by',1)[0]
        assert statement==adapted.split(':= by',1)[0]
        assert sha(statement.encode())==adaptation['unchanged_statement_sha256']
        retained=retained.replace(original,adapted)
    assert retained.encode()==(root/row['file']).read_bytes()
    assert sha(retained.encode())==row['retained_file_sha256']
provenance=json.loads((root/'source-provenance.json').read_text())
assert len(provenance['excerpts'])==3
assert provenance['upstream_commit']=='ea1367d99c7d2f3794f1299cce5b18379e9093a7'
authenticated=0
if args.upstream_root:
    upstream_git=lambda *xs:subprocess.check_output(['git','-C',str(args.upstream_root),*xs])
    assert upstream_git('rev-parse','HEAD').decode().strip()==provenance['upstream_commit']
    for row in provenance['excerpts']:
        raw=upstream_git('show',provenance['upstream_commit']+':'+row['path'])
        assert raw==(args.upstream_root/row['path']).read_bytes() and sha(raw)==row['source_sha256']
        text=raw.decode();begin=text.index(row['start_marker']);end=text.index(row['end_marker'])
        excerpt=text[begin:end].rstrip()+'\n'
        assert sha(excerpt.encode())==row['excerpt_sha256'] and excerpt in (root/'SourcePaths.lean').read_text()
        assert text[:begin].count('\n')+1==row['first_line']
        assert row['last_line']==row['first_line']+len(excerpt.splitlines())-1
        authenticated+=1
sound=json.loads((root/'realization-provenance.json').read_text())
assert sound['commit']==provenance['upstream_commit']
if args.upstream_root:
    raw=upstream_git('show',sound['commit']+':'+sound['path'])
    assert raw==(args.upstream_root/sound['path']).read_bytes() and sha(raw)==sound['source_sha256']
    excerpt=raw.decode()[sound['start_char']:sound['end_char_exclusive']]
    assert sha(excerpt.encode())==sound['excerpt_sha256']
    assert excerpt in (root/sound['target']).read_text()
    authenticated+=1
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
packages=json.loads((root/'lake-manifest.json').read_text())['packages']
assert next(package for package in packages if package['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
config=json.loads((root/'comparator.json').read_text())
assert (len(config['theorem_names']),len(config['definition_names']))==(24,21)
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
for path in root.glob('*.lean'):
    text=erase_comments(path.read_text())
    assert text.lstrip().startswith('module'),path.name
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|set_option)\b',text),path.name
meta=json.loads((root/'formalization.yaml').read_text())
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert meta['status']['axioms']==config['permitted_axioms']
assert 'analytic' in meta['status']['known_gaps'] and 'kernel' in meta['status']['scope']
subprocess.run(['python3',str(repository/'scripts/check_imported_definitions.py'),'--project-path',str(root),'--dependency-root',str(root/'.lake/packages/mathlib')],check=True)
print(json.dumps(dict(status='pass',base_files_git_authenticated=len(base['files']),upstream_excerpts_git_authenticated=authenticated,scope='Consistency and retained-source provenance only. Semantic completeness, native/canonical/kernel/render/visual checks and independent review have separately bound receipts.'),indent=2))
