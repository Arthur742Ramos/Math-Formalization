"""Compile fresh proofs, an isolated Challenge, exact types and predicate values.

Use --lake-build to retrieve the pinned cache and perform an ordinary Lake build.
This verifies with Lean; it does not claim a hosted Comparator or NanoDa run.
"""
from __future__ import annotations
import argparse, ctypes, hashlib, json, os, re, shutil, subprocess, tempfile, uuid
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
PIN='065356127b1dc0016f66b7283ce0ce2c4055aa55'
TOOLCHAIN='leanprover/lean4:v4.35.0-rc2'
NAMES=['WhitneyReversibility.isCompact_relativeLevel', 'WhitneyReversibility.isConnected_relativeLevel', 'WhitneyReversibility.familyUnion_relativeLevel', 'WhitneyReversibility.exists_indecomposable_covering_family', 'WhitneyReversibility.sequential_strong_whitney_reversibility']
PREDICATES=['WhitneyReversibility.Continuum', 'WhitneyReversibility.singleton', 'WhitneyReversibility.whole', 'WhitneyReversibility.IsWhitneyMap', 'WhitneyReversibility.IsSizeMap', 'WhitneyReversibility.relativeLevel', 'WhitneyReversibility.familyUnion', 'WhitneyReversibility.IsDecomposable', 'WhitneyReversibility.IsHereditarilyDecomposable']
PREFIX=""
IMPORTS=['Mathlib.Topology.MetricSpace.Closeds', 'Mathlib.Topology.UnitInterval', 'Mathlib.Topology.Connected.Clopen']
MODULES=['Boundary', 'Checkpoint', 'Scalar', 'Hyperspace', 'Chain', 'Parameter', 'OrderArc', 'Levels', 'Reduction', 'Solution']
AUDITED=['WhitneyReversibility.isCompact_relativeLevel', 'WhitneyReversibility.isConnected_relativeLevel', 'WhitneyReversibility.familyUnion_relativeLevel', 'WhitneyReversibility.exists_indecomposable_covering_family', 'WhitneyReversibility.sequential_strong_whitney_reversibility', 'WhitneyReversibility.Continuum', 'WhitneyReversibility.singleton', 'WhitneyReversibility.whole', 'WhitneyReversibility.IsWhitneyMap', 'WhitneyReversibility.IsSizeMap', 'WhitneyReversibility.relativeLevel', 'WhitneyReversibility.familyUnion', 'WhitneyReversibility.IsDecomposable', 'WhitneyReversibility.IsHereditarilyDecomposable', 'WhitneyReversibility.connected_square_level', 'WhitneyReversibility.connected_relativeLevel_pair', 'WhitneyReversibility.isConnected_anchored_relativeLevel', 'WhitneyReversibility.exists_minimal_covering_family', 'WhitneyReversibility.minimal_covering_family_indecomposable']
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean-bin',default=shutil.which('lean'))
parser.add_argument('--lake-build',action='store_true')
parser.add_argument('--check-package-only',action='store_true')
parser.add_argument('--output',type=Path,default=ROOT/'verification.json')
args=parser.parse_args()
report={'status':'fail','scope':'Fresh local Lean verification, not hosted Comparator or NanoDa',
        'stages':[],'source_sha256':{}}
def sha(data):return hashlib.sha256(data).hexdigest()
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
for name in [n+'.lean' for n in MODULES]+['Challenge.lean','lake-manifest.json','lakefile.toml','lean-toolchain','comparator.json']:
    report['source_sha256'][name]=sha((ROOT/name).read_bytes())
for path in ROOT.rglob('*.lean'):
    if '.lake' in path.parts:continue
    text=path.read_text(encoding='utf-8')
    header=re.sub(r'\A\s*/-.*?-/\s*','',text,count=1,flags=re.S)
    assert header.startswith('module\n') and len(text.splitlines())<=10000,path
solution='\n'.join((ROOT/n).read_text(encoding='utf-8') for n in [m+'.lean' for m in MODULES])
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',solution)
challenge=(ROOT/'Challenge.lean').read_text(encoding='utf-8')
assert len(challenge.encode())<16384 and len(challenge.splitlines())<=150
assert re.findall(r'^(?:(?:public|private|meta) )*import (.+)$',challenge,re.M)==IMPORTS
assert len(re.findall(r'\bsorry\b',challenge))==len(NAMES)
config=json.loads((ROOT/'comparator.json').read_text())
assert config['theorem_names']==[PREFIX+n for n in NAMES] and config['definition_names']==[PREFIX+n for n in PREDICATES]
assert set(config['permitted_axioms'])=={'propext','Quot.sound','Classical.choice'}
assert (ROOT/'lean-toolchain').read_text().strip()==TOOLCHAIN
assert next(p for p in manifest['packages'] if p['name']=='mathlib')['rev']==PIN
print('PACKAGE CHECKS PASS',flush=True)
if args.check_package_only:raise SystemExit(0)
if not args.lean_bin:parser.error('Supply --lean-bin or install the pinned toolchain')
if os.name=='nt':
    k=ctypes.WinDLL('kernel32',use_last_error=True);k.GetCurrentProcess.restype=ctypes.c_void_p
    handle=ctypes.c_void_p(k.GetCurrentProcess());pm,sm=ctypes.c_size_t(),ctypes.c_size_t()
    assert k.GetProcessAffinityMask(handle,ctypes.byref(pm),ctypes.byref(sm))
    assert k.SetProcessAffinityMask(handle,ctypes.c_size_t(pm.value & -pm.value))
elif hasattr(os,'sched_getaffinity'):os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:1])
prefix=subprocess.check_output([args.lean_bin,'--print-prefix'],text=True).strip()
lean=Path(prefix)/'bin'/('lean.exe' if os.name=='nt' else 'lean')
env=dict(os.environ);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
env['LEAN_NUM_THREADS']='1';env['LEAN_PATH']='';env.pop('LEAN_SRC_PATH',None)
version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
assert 'version 4.35.0-rc2,' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version
report.update(lean_version=version,lean_binary_sha256=sha(lean.read_bytes()))
def command(stage,argv,cwd,environment):
    result=subprocess.run(argv,cwd=cwd,env=environment,encoding='utf-8',stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,timeout=1800)
    report['stages'].append({'stage':stage,'argv':argv,'cwd':str(cwd),'exit_code':result.returncode,'output':result.stdout})
    print(stage,flush=True);print(result.stdout,end='',flush=True)
    assert result.returncode==0,stage
    return result.stdout
def run(stage,extra,cwd,environment):
    return command(stage,[str(lean),'-j1','-M3072',*map(str,extra)],cwd,environment)
try:
    if args.lake_build:
        lake=lean.parent/('lake.exe' if os.name=='nt' else 'lake')
        command('pinned Mathlib cache',[str(lake),'exe','cache','get'],ROOT,env)
        command('ordinary Lake build',[str(lake),'build','--wfail'],ROOT,env)
        assert sha((ROOT/'lake-manifest.json').read_bytes())==report['source_sha256']['lake-manifest.json']
    deps=[ROOT/manifest.get('packagesDir','.lake/packages')/p['name']/'.lake/build/lib/lean' for p in manifest['packages']]
    deps=[p.resolve() for p in deps if p.is_dir()]
    assert deps,'No local dependencies; use --lake-build'
    for p in deps:
        for name in MODULES+['Challenge','OrderArcs']:
            assert not (p/(name+'.olean')).exists() and not (p/name).exists(),'contaminated dependency path'
    env['LEAN_PATH']=os.pathsep.join(map(str,deps));report['dependency_paths']=list(map(str,deps))
    with tempfile.TemporaryDirectory(prefix='whitney-reversibility-check-') as temp:
        folder=Path(temp)
        proof_env=dict(env);proof_env['LEAN_PATH']=str(folder)+os.pathsep+env['LEAN_PATH']
        for module in MODULES:
            run('fresh strict '+module,['-DwarningAsError=true','-o',folder/(module+'.olean'),ROOT/(module+'.lean')],ROOT,proof_env)
        canonical='CanonicalChallenge_'+uuid.uuid4().hex
        (folder/(canonical+'.lean')).write_bytes((ROOT/'Challenge.lean').read_bytes())
        output=run('isolated dependency-only Challenge',['-o',canonical+'.olean',canonical+'.lean'],folder,env)
        assert output.count('declaration uses `sorry`')==len(NAMES)
        imported=dict(env);imported['LEAN_PATH']=str(folder)+os.pathsep+env['LEAN_PATH']
        raw_c=run('raw Challenge declarations',['--run',ROOT/'scripts/CompareTypes.lean',canonical],folder,imported)
        raw_s=run('raw Solution declarations',['--run',ROOT/'scripts/CompareTypes.lean','Solution'],folder,imported)
        assert raw_c==raw_s,'Exact type, universe or literal definition value mismatch'
        report['exact_comparison']={'theorems':len(NAMES),'literal_definitions':len(PREDICATES),'raw_expression_sha256':sha(raw_s.encode()),
            'method':'Byte equality of raw Lean.Expr, universe parameter lists, and definition values in separate imports'}
        semantic=run('literal predicates, singleton edge and transitive axiom audit',
            ['-DwarningAsError=true',ROOT/'scripts/SemanticAudit.lean'],folder,imported)
        audits=re.findall(r'(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)',semantic)
        assert len(audits)==len(AUDITED)
        assert all({n.strip() for n in a.split(',') if n.strip()}<=set(config['permitted_axioms']) for a in audits)
        report['transitive_axioms']=dict(zip(AUDITED,audits))
        run('literal pinned path and hyperspace predicates',['-DwarningAsError=true',ROOT/'scripts/DefinitionAudit.lean'],ROOT,env)
        report['status']='pass'
finally:
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('ALL LOCAL LEAN GATES PASS',flush=True)
