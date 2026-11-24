# verify2: re-run stage2/r3_survey.py with an independent, multiplicity-robust linear-factor finder for the cubics c_S.
# Method: polarisation T(a,b,c) of the cubic (exact formula); roots of c on a generic 2-plane; for each root w the candidate factor is
# grad c(w) (simple factor), or the dominant singular vector of Hess c(w) (double factor), or grad c at a generic point (triple factor);
# every candidate is verified by evaluating c on its kernel. Multiple roots are refined through the derivative polynomials.
import sys, itertools, importlib.util, numpy as np
spec=importlib.util.spec_from_file_location('r3s','/home/kevxhk/work/L-gct-210/stage2/r3_survey.py'); r3=importlib.util.module_from_spec(spec); spec.loader.exec_module(r3)
rng=np.random.default_rng(99)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
old=r3.linfactors; diff=[]; nfac={'old':0,'new':0}
def robust(cfun,d):
    def T(a,b,c): return (cfun(a+b+c)-cfun(a+b)-cfun(a+c)-cfun(b+c)+cfun(a)+cfun(b)+cfun(c))/6
    E=np.eye(d)
    scale=max(abs(cfun(rnd(d))) for _ in range(6))
    if scale<1e-9: return None
    grad=lambda w: np.array([3*T(w,w,E[k]) for k in range(d)])
    hess=lambda w: np.array([[6*T(w,E[k],E[l]) for l in range(d)] for k in range(d)])
    cands=[]
    for trial in range(3):
        p=rnd(d); q=rnd(d)
        # binary cubic c(p + s q) = c0 + c1 s + c2 s^2 + c3 s^3
        co=[cfun(q),3*T(p,q,q),3*T(p,p,q),cfun(p)]          # s^3, s^2, s^1, s^0
        roots=list(np.roots(co))
        # refine clustered roots through derivatives
        ref=[]
        for r in roots:
            close=[x for x in roots if abs(x-r)<1e-3*max(1,abs(r))]
            if len(close)==2:
                dr=np.roots(np.polyder(co)); r=min(dr,key=lambda x:abs(x-r))
            elif len(close)==3:
                dr=np.roots(np.polyder(np.polyder(co))); r=dr[0]
            ref.append(r)
        for s in ref:
            w=p+s*q; g=grad(w)
            if np.abs(g).max()>1e-6*scale: cands.append(g)
            else:
                H=hess(w)
                if np.abs(H).max()>1e-6*scale: cands.append(np.linalg.svd(H)[2][0].conj())   # H ~ l l^T: right singular vector ~ conj? handle both
                else: cands.append(grad(rnd(d)))
    facs=[]
    for lam in cands:
        for l in (lam,lam.conj()):
            if np.abs(l).max()<1e-12: continue
            l=l/np.linalg.norm(l)
            Hb=np.linalg.svd(l[None,:])[2][1:].conj().T          # basis of {v : l.v = 0} (bilinear pairing)
            if np.abs(l@Hb).max()>1e-9: Hb=r3.nullspace(l[None,:])
            if all(abs(cfun(Hb@rnd(d-1)))<1e-6*scale for _ in range(5)) and not any(r3.rank(np.array([l,f]))==1 for f in facs): facs.append(l)
    return facs
def both(cfun,d):
    a=old(cfun,d); b=robust(cfun,d)
    if (a is None)!=(b is None) or (a is not None and len(a)!=len(b)): diff.append((d,None if a is None else len(a),None if b is None else len(b)))
    if a is not None: nfac['old']+=len(a)
    if b is not None: nfac['new']+=len(b)
    return b
r3.linfactors=both
stats={}; surv=[]
for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
    s12=(tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1)
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        for eps in (1,-1):
            r=r3.analyse(s12,(cells,eps)); key=r if isinstance(r,str) else r[0]; stats[key]=stats.get(key,0)+1
            if key=='SURVIVES': surv.append((s12,(cells,eps),r))
print('with the robust factor finder:',stats)
print('total linear factors found: stage2 finder %d, robust finder %d; cubics where the counts differ: %d'%(nfac['old'],nfac['new'],len(diff)))
print('differences (dim K_S, old count, new count):',diff[:20])
for s in surv: print('  ',s)
