"""Check catalog truth, immutable package trees and public registration records."""
import argparse,hashlib,json,pathlib,re,subprocess,sys,urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[1]
HEX=re.compile(r'[0-9a-f]{40}')
STATUSES={'registered','registration-pending','no-public-registration-found'}

def git(*args):
    return subprocess.check_output(['git','-C',str(ROOT),*args]).decode('utf-8').strip()

def check(online,packages):
    data=json.loads((ROOT/'REGISTRATIONS.json').read_text(encoding='utf-8'))
    assert data['schema_version']==1
    assert data['repository']=='Arthur742Ramos/Math-Formalization'
    assert re.fullmatch(r'\d{4}-\d{2}-\d{2}',data['checked_date'])
    assert isinstance(data['registry_revision'],int)
    assert re.fullmatch(r'[0-9a-f]{64}',data['registry_release'])
    rows=[s for s in (ROOT/'PROJECTS.md').read_text(encoding='utf-8').splitlines() if s.startswith('| [')]
    expected_paths=set(git('ls-tree','--name-only','HEAD:topology').splitlines())
    seen=set();records=[];package_checks=[]
    for project in data['projects']:
        assert set(project)=={'name','path','scope','source_snapshot','status'} | ({'registration'} if project['status']=='registered' else set())
        path=project['path'];assert re.fullmatch(r'topology/[a-z0-9-]+',path)
        assert path not in seen;seen.add(path)
        snapshot=project['source_snapshot'];pin=snapshot['commit'];tree=snapshot['tree']
        assert HEX.fullmatch(pin) and HEX.fullmatch(tree)
        assert git('rev-parse',pin+':'+path)==tree,(path,'snapshot tree')
        assert git('rev-parse','HEAD:'+path)==tree,(path,'project changed')
        subprocess.run(['git','-C',str(ROOT),'merge-base','--is-ancestor',pin,'HEAD'],check=True)
        matching=[row for row in rows if ']('+path+')' in row]
        assert len(matching)==1,(path,'catalog row')
        row=matching[0]
        assert project['name'] in row and project['scope'] in row
        assert f'https://github.com/{data["repository"]}/tree/{pin}/{path}' in row
        status=project['status'];assert status in STATUSES
        if status=='registered':
            r=project['registration'];identifier=r['id'];version=r['version']
            assert re.fullmatch(r'PALOMAR-\d{4}-\d{2}-\d{2}-\d{6}',identifier)
            assert isinstance(version,int) and version>0
            assert r['source_commit']==pin
            assert r['url']==f'https://palomar-registry.org/entry.html?id={identifier}&version={version}'
            assert r['record_url']==f'https://data.palomar-registry.org/entries/{identifier}-v{version}.json'
            config=json.loads((ROOT/path/'comparator.json').read_text(encoding='utf-8'))
            assert r['theorem_names']==config['theorem_names']
            assert f'Registered: [{identifier} v{version}]({r["url"]})' in row
            if online:
                request=urllib.request.Request(r['record_url'],headers={'User-Agent':'Math-Formalization catalog checker','Accept':'application/json'})
                with urllib.request.urlopen(request,timeout=30) as response:body=response.read()
                official=json.loads(body)
                assert official['id']==identifier and official['version']==version and official['status']=='registered'
                assert official['source']['repository']==data['repository']
                assert official['source']['project_path']==path and official['source']['commit']==pin
                assert official['formalization']['theorem_names']==r['theorem_names']
                records.append({'id':identifier,'record_sha256':hashlib.sha256(body).hexdigest()})
        else:
            label='Registration pending' if status=='registration-pending' else 'No public registration found'
            assert label in row and 'PALOMAR-' not in row
        if packages:
            directory=ROOT/path
            verifier=directory/'scripts/verify.py';checker=directory/'scripts/check_package.py'
            if verifier.exists():command=[sys.executable,str(verifier),'--check-package-only']
            else:
                assert checker.exists(),path
                command=[sys.executable,str(checker)]
                axioms=directory/'verification/local-axioms.txt'
                if axioms.exists():command+=['--axiom-log',str(axioms)]
            result=subprocess.run(command,cwd=directory,capture_output=True,text=True)
            assert result.returncode==0,(path,result.stdout[-1500:],result.stderr[-1500:])
            package_checks.append(path)
    assert {p.removeprefix('topology/') for p in seen}==expected_paths
    assert len(rows)==len(seen)
    for file in ['README.md','PROJECTS.md']:
        text=(ROOT/file).read_text(encoding='utf-8')
        assert not re.search(r'<<<<<<<|>>>>>>>|\bsubmission_id\b|\bauthorization_challenge\b',text)
        for target in re.findall(r'\]\(([^)]+)\)',text):
            if target.startswith('https://'):continue
            resolved=(ROOT/target).resolve()
            assert resolved.is_relative_to(ROOT) and resolved.exists(),(file,target)
    sources=git('ls-tree','-r','--name-only','HEAD').splitlines()
    lean=[name for name in sources if name.endswith('.lean')]
    for name in lean:
        body=subprocess.check_output(['git','-C',str(ROOT),'show','HEAD:'+name]).decode('utf-8')
        assert re.search(r'^module\s*$',body,re.M),name
        assert len(body.splitlines())<=10000,name
    subprocess.run([sys.executable,str(ROOT/'scripts/check_readiness.py')],check=True)
    print(json.dumps({'status':'pass','commit':git('rev-parse','HEAD'),'projects':len(seen),'registered':sum(p['status']=='registered' for p in data['projects']),'preserved_package_trees':len(seen),'lean_source_headers_checked':len(lean),'package_consistency_checks':package_checks,'public_records_checked':records,'scope':'Catalog, preserved source trees and existing package consistency checks. No Lean build or new Palomar review.'},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--online',action='store_true');parser.add_argument('--package-checks',action='store_true');args=parser.parse_args();check(args.online,args.package_checks)
