from pathlib import Path
import hashlib,json,re
if not __debug__:
    raise RuntimeError('This checker must run without Python optimization')
root=Path(__file__).resolve().parents[1]
def erase_comments_and_strings(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            e=s.find('\n',i);i=len(s) if e<0 else e
        elif s[i]=='"':
            i+=1
            while i<len(s):
                if s[i]=='\\':i+=2
                elif s[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)
rows=[]
for p in sorted(root.glob('*.lean')):
    raw=p.read_bytes();s=erase_comments_and_strings(raw.decode())
    assert s.lstrip().startswith('module'),p.name
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|set_option)\b',s),p.name
    rows.append({'file':p.name,'sha256':hashlib.sha256(raw).hexdigest()})
assert len(rows)==7
print(json.dumps({'status':'pass','files':rows,'scope':'Static source-token scan only; transitive axiom, compiler, canonical and independent kernel checks are separate.'},indent=2))
