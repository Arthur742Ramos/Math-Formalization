#!/usr/bin/env python3
"""Rebuild the formal certificate in a clean directory with an actual Lean kernel.

Requires Lean 4.35.0-rc2, Python 3.10+, and Std shipped with Lean. No Mathlib or
external solver is used. On the managed executor only, the narrow supplied
/proc/self compatibility shim is built when its necessity is observed.
"""
from pathlib import Path
import argparse, concurrent.futures, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

HERE = Path(__file__).resolve().parent
STANDARD_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
STAGES = [
    ['BaseWitnesses','DigitLemmas','ArithmeticCertificate','F3Linear','ProfileEnumeration',
     'PairedLift','TransformSoundness','Known63Witness','Cyclic45Obstruction'],
    ['ProfileData','CertifiedLinear','ExceptionalProfile'],
    [f'ProfileCheck{i:02}' for i in range(17)],
    ['ProfileCoverage'],
    ['ArithmeticExclusion'],
    [f'TriangleBatch{i:02}' for i in range(17)],
    ['Normalization'], ['CoveringNormalization'], ['RepresentativeExtension'],
    ['RepresentativeEligibility'], ['DigitTransport'],
]

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
    return h.hexdigest()

def source_code(s):
    """Remove nested block and line comments before the forbidden-token audit."""
    out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    if depth:raise ValueError('Unclosed Lean block comment')
    return ''.join(out)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',help='Path to the actual Lean 4.35.0-rc2 executable')
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--timeout',type=int,default=120,help='Seconds per module')
    ap.add_argument('--report',type=Path,default=HERE/'verification_report.json')
    a=ap.parse_args()
    if not 1<=a.jobs<=4:ap.error('--jobs must be 1 through 4')
    local=HERE.parents[1]/'lean-runtime/lean-4.35.0-rc2-linux/bin/lean'
    lean=a.lean or shutil.which('lean') or (str(local) if local.is_file() else None)
    if not lean:ap.error('Lean is not installed; supply --lean PATH. No formal success is claimed.')
    lean=str(Path(shutil.which(lean) or lean).resolve())
    inputs={p.name:sha(p) for p in HERE.glob('*.lean') if p.stem in {m for st in STAGES for m in st}}
    for filename in inputs:
        code=source_code((HERE/filename).read_text())
        if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b',code,re.M):
            raise ValueError('Forbidden proof placeholder/oracle/declaration in '+filename)
    t0=time.monotonic();records=[]
    with tempfile.TemporaryDirectory(prefix='_lean_check_',dir=HERE) as td:
        build=Path(td);env=os.environ.copy();env['LEAN_PATH']=str(build)
        version=subprocess.run([lean,'--version'],capture_output=True,text=True,env=env,timeout=15)
        shim=False
        if version.returncode and 'failed to locate application' in version.stdout+version.stderr and sys.platform.startswith('linux'):
            # This is a compatibility repair for equivalent own-process paths,
            # not a theorem checker modification or network/access override.
            os.readlink('/proc/self/exe')
            try:os.readlink('/proc/'+str(os.getpid())+'/exe')
            except (FileNotFoundError, PermissionError):
                cc=shutil.which('cc')
                if not cc:raise RuntimeError('C compiler needed for observed /proc namespace incompatibility')
                shim_path=build/'proc_self_compat.so'
                subprocess.run([cc,'-shared','-fPIC','-O2','-o',str(shim_path),str(HERE/'proc_self_compat.c'),'-ldl'],check=True,capture_output=True,text=True,timeout=30)
                previous=env.get('LD_PRELOAD','')
                env['LD_PRELOAD']=str(shim_path)+(':'+previous if previous else '')
                shim=True
            version=subprocess.run([lean,'--version'],capture_output=True,text=True,env=env,timeout=15)
        if version.returncode:raise RuntimeError(version.stdout+version.stderr)
        version_text=version.stdout.strip()
        if 'version 4.35.0-rc2,' not in version_text:
            raise RuntimeError('Pinned Lean 4.35.0-rc2 required; got '+version_text)
        logs=HERE/'logs';logs.mkdir(exist_ok=True)
        def check(name):
            src=HERE/(name+'.lean');start=time.monotonic()
            cmd=[lean,'-s','65536','-o',str(build/(name+'.olean')),str(src)]
            try:
                result=subprocess.run(cmd,cwd=HERE,env=env,capture_output=True,text=True,timeout=a.timeout)
                output=result.stdout+result.stderr;exit_code=result.returncode
            except subprocess.TimeoutExpired as e:
                output='TIMEOUT\n'+(e.stdout or b'').decode()+(e.stderr or b'').decode();exit_code=124
            log=logs/(name+'.log');log.write_text(output)
            axioms=[]
            for line in output.splitlines():
                m=re.fullmatch(r"'([^']+)' does not depend on any axioms",line)
                if m:axioms.append({'declaration':m.group(1),'axioms':[]});continue
                m=re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]",line)
                if m:axioms.append({'declaration':m.group(1),'axioms':[x.strip() for x in m.group(2).split(',') if x.strip()]})
            clean=(exit_code==0 and 'error:' not in output and axioms and
                   all(set(x['axioms'])<=STANDARD_AXIOMS for x in axioms))
            d={'module':name,'status':'PASS' if clean else 'FAIL','exit_code':exit_code,
               'seconds':round(time.monotonic()-start,6),'source_sha256':sha(src),
               'log_file':str(log.relative_to(HERE)),'log_sha256':sha(log),'axiom_reports':axioms}
            print(json.dumps({'module':name,'status':d['status'],'seconds':d['seconds']}),flush=True)
            return d
        for stage in STAGES:
            with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
                stage_records=list(pool.map(check,stage))
            records.extend(stage_records)
            if not all(r['status']=='PASS' for r in stage_records):break
        unchanged=all(sha(HERE/name)==h for name,h in inputs.items())
        report={'format':'covering-schemes-lean-certificate-v1',
            'status':'PASS' if unchanged and len(records)==sum(map(len,STAGES)) and all(r['status']=='PASS' for r in records) else 'FAIL',
            'lean_version':version_text,'lean_executable':lean,'lean_executable_sha256':sha(lean),
            'proc_self_compatibility_applied':shim,'compatibility_source_sha256':sha(HERE/'proc_self_compat.c'),
            'thread_stack_kib':65536,'jobs':a.jobs,'per_module_timeout_seconds':a.timeout,
            'elapsed_seconds':round(time.monotonic()-t0,6),'source_files_unchanged':unchanged,
            'inputs':inputs,'modules':records,
            'scope':'Kernel checks of the declarations listed in the per-module logs. The proof coverage manifest states the remaining mathematical bridges. This is not a blanket formalization of the entire manuscript.'}
        a.report.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({'status':report['status'],'modules':len(records),'seconds':report['elapsed_seconds'],'report':str(a.report)}),flush=True)
        if report['status']!='PASS':raise SystemExit(1)

if __name__=='__main__':main()
