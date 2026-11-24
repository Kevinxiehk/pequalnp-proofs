# Common rank-drop locus via msolve mod p (STRUCTURE / evidence; exact certificate later) [NOTES-stage2 R16]. Same input as r16_cofint_sing.py.
import sys, re, itertools, subprocess, os, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
txt=open(sys.argv[1]).read(); p=2147483629
par=[q.strip(" '") for q in re.search(r'parameters \[(.*?)\]',txt).group(1).split(',')]; S={q:sp.Symbol(q) for q in par}
exc=sp.sympify(re.search(r'setup-exceptional factors: (\[.*\])',txt).group(1),locals=S)
fams=[sp.sympify(m,locals=S) for m in re.findall(r'non-exceptional factors: (\[.*\])',txt)]
w=sp.Symbol('w'); vv=[S[q] for q in par]+[w]; E=sp.expand(sp.prod(exc))
wd='/tmp/st2_cofms_%d'%os.getpid(); os.makedirs(wd,exist_ok=True)
for ch in itertools.product(*fams):
    polys=list(dict.fromkeys(sp.expand(f) for f in ch))+[sp.expand(w*E-1)]
    fn=wd+'/c.ms'; out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write(','.join(map(str,vv))+'\n%d\n'%p+',\n'.join(msstr(q,vv,p) for q in polys)+'\n')
    subprocess.run('ulimit -v 2000000; timeout 300 msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
    res=open(out).read() if os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn) else 'FAILED'
    body=re.sub(r'\s','',''.join(l for l in res.splitlines() if not l.startswith('#')))
    tag=[str(f)[:25] for f in ch]
    if body=='[1]:': print('empty   ',tag,flush=True)
    else: print('NONEMPTY',tag,' GB head:',body[:300],flush=True)
