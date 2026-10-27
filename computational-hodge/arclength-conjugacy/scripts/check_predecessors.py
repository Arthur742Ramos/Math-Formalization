#!/usr/bin/env python3
"""Authenticate the exact reviewed predecessor mappings; no proof is inferred from hashes."""
from pathlib import Path
import hashlib,json,os,subprocess
os.environ['GIT_OPTIONAL_LOCKS']='0'
root=Path(__file__).resolve().parents[1]
repository=root.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=root/'base-provenance.json'
assert sha(manifest.read_bytes())=='4af179cfd875bd14e7d4ab5989c92f004347e2247821e153e9d1253a392b5257'
v=json.loads(manifest.read_text());commit='73ee0d0c2f25a2191edf15e14e124c8f8cfeb467'
assert v['source_commit']==commit and v['repository']=='Arthur742Ramos/Math-Formalization'
expected=['SourcePaths','Periods','Harmonic','LoopImage','CircleWinding','CircleData','RawLift','CirclePeriods','ACAnalysis','ACPeriods','Potential','Density','Poisson','Green','Fredholm','Resonance','ArclengthCoordinate']
assert [x['path'] for x in v['modules']]==[x+'.lean' for x in expected]
for row in v['modules']:
    module=row['path'][:-5]
    expected_path=('computational-hodge/arclength/Arclength.lean' if module=='ArclengthCoordinate' else 'computational-hodge/resonance-obstruction/'+row['path'])
    assert row['source_path']==expected_path
    assert row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+expected_path
    raw=subprocess.check_output(['git','-C',str(repository),'show',commit+':'+expected_path])
    assert sha(raw)==row['source_sha256']
    lines=raw.decode().splitlines(keepends=True);rebuilt=[];cursor=0
    for op in row['operations']:
        a=op['source_first_line']-1;b=op['source_last_line'];assert a==cursor and a<=b;cursor=b
        if op['operation']=='equal':
            part=''.join(lines[a:b]);assert sha(part.encode())==op['sha256'];rebuilt.append(part)
        else:
            assert op['operation'] in ['replace','delete','insert']
            assert sha(''.join(lines[a:b]).encode())==op['removed_source_sha256']
            assert sha(op['added_text'].encode())==op['added_sha256'];rebuilt.append(op['added_text'])
    assert cursor==len(lines)
    result=''.join(rebuilt).encode();assert sha(result)==row['candidate_sha256'] and (root/row['path']).read_bytes()==result
print(json.dumps({'status':'pass','commit':commit,'modules':len(v['modules']),'scope':'Exact pinned predecessor mapping; source and semantic review remain separate.'}))
