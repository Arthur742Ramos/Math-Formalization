#!/usr/bin/env python3
"""Authenticate the exact reviewed predecessor mappings; no proof is inferred from hashes."""
from pathlib import Path
import hashlib,json,os,subprocess
os.environ['GIT_OPTIONAL_LOCKS']='0'
root=Path(__file__).resolve().parents[1]
repository=root.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=root/'base-provenance.json'
assert sha(manifest.read_bytes())=='fbfe5cade383b5b7ec38f13c7e6efded8ba2414e844284773034bf2769b84b3e'
v=json.loads(manifest.read_text());commit='2b7444b551a9a6f8c4e3fe1de51bc7debe614c6d'
assert v['source_commit']==commit and v['repository']=='Arthur742Ramos/Math-Formalization'
expected=['SourcePaths', 'Periods', 'Harmonic', 'LoopImage', 'CircleWinding', 'CircleData', 'RawLift', 'CirclePeriods', 'ACAnalysis', 'ACPeriods', 'Potential', 'Density', 'Poisson', 'Green', 'Fredholm', 'Resonance', 'ArclengthCoordinate', 'CoordinateRegularity', 'Conjugacy', 'TracePhase']
assert [x['path'] for x in v['modules']]==[x+'.lean' for x in expected]
for row in v['modules']:
    module=row['path'][:-5]
    expected_path='computational-hodge/arclength-conjugacy/'+row['path']
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
            assert ''.join(lines[a:b])==op['removed_text']
            assert sha(op['added_text'].encode())==op['added_sha256'];rebuilt.append(op['added_text'])
    assert cursor==len(lines)
    result=''.join(rebuilt).encode();assert sha(result)==row['candidate_sha256'] and (root/row['path']).read_bytes()==result
for row in v['omitted_modules']:
    assert row['path'].startswith('computational-hodge/arclength-conjugacy/')
    assert row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+row['path']
    raw=subprocess.check_output(['git','-C',str(repository),'show',commit+':'+row['path']])
    assert sha(raw)==row['source_sha256'] and raw.decode()==row['complete_text']
    assert not (root/Path(row['path']).name).exists()
assert [Path(x['path']).stem for x in v['omitted_modules']]==['CircleCoordinate','ArclengthMode','NonflatExample','FirstPathMode']
print(json.dumps({'status':'pass','commit':commit,'modules':len(v['modules']),'scope':'Exact pinned predecessor mapping; source and semantic review remain separate.'}))
