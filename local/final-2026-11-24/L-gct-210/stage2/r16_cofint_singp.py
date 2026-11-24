# [char 32003 version: STRUCTURE only (dim, vdim)] Common rank-drop locus via Singular [NOTES-stage2 R16]: from a r16_Kauto.py log take the per-sample non-exceptional factor lists,
# and for every choice of one factor per sample compute  std( factors + (1 - w * prod(exceptional)) )  ; print dim and the basis of the
# non-empty ones (after eliminating w).  usage: r16_cofint_sing.py KAUTO_LOG
import sys, re, itertools, subprocess, os, sympy as sp
txt=open(sys.argv[1]).read()
par=[p.strip(" '") for p in re.search(r'parameters \[(.*?)\]',txt).group(1).split(',')]
S={p:sp.Symbol(p) for p in par}
exc=sp.sympify(re.search(r'setup-exceptional factors: (\[.*\])',txt).group(1),locals=S)
fams=[sp.sympify(m,locals=S) for m in re.findall(r'non-exceptional factors: (\[.*\])',txt)]
print('parameters',par,' samples',len(fams),' exceptional',exc,flush=True)
wd='/tmp/st2_cofint_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); comps=set()
for ch in itertools.product(*fams):
    polys=sorted(set(str(sp.expand(f)) for f in ch))
    E=sp.expand(sp.prod(exc)) if exc else 1
    fn=wd+'/c.sing'; out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write('ring r=32003,(w,%s),dp;\nideal I=%s,1-w*(%s);\nideal J=eliminate(std(I),w);\nring s=32003,(%s),dp;\nideal J=imap(r,J);\nJ=std(J);\nwrite(":w %s", string(dim(J))+"|"+string(vdim(J))+"|"+string(size(J)));\nquit;\n'%(','.join(par),','.join(polys),str(E).replace('**','^'),','.join(par),out))
    subprocess.run('ulimit -v 2000000; timeout 300 Singular -q %s > /dev/null 2>&1'%fn,shell=True)
    res=open(out).read().strip() if os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn) else 'FAILED'
    if res=='FAILED': print('FAILED combination',polys,flush=True); comps.add('FAILED '+str(polys)); continue
    d,J=res.split('|',1)
    if d!='-1': comps.add('dim %s: %s'%(d,J))
print('COMMON RANK-DROP LOCUS components (outside exceptional):',flush=True)
for c in sorted(comps): print('   ',c[:600],flush=True)
