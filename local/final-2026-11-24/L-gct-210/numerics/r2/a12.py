import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
from a11 import hyperplanes
jobs=[a.split(':') for a in sys.argv[1].split(',')]; e=int(sys.argv[2]); starts=int(sys.argv[3]); tl=float(sys.argv[4])
def get(nm): return {'L080':L080(),'ex1':ex1(),'ex2':ex2(),'ex3':ex3()}.get(nm) if nm in ('L080','ex1','ex2','ex3') else np.load(nm+'.npy')
for nm,lab in jobs:
    B=get(nm); S=dict(hyperplanes(B))[lab]; dS,ES,_=ext_space(S)
    rng=np.random.default_rng(7); res=[]; t0=time.time()
    for st in range(starts):
        sB=np.einsum('ij,jab->iab',rng.normal(size=(e,dS))+1j*rng.normal(size=(e,dS)),ES)
        fc,Bn=lm_space(sB,6+e,fixed=S,ambient=ES,iters=150,tlimit=tl,rng=rng,rounds=3)
        res.append(fc)
        if fc<1e-10: np.save(f'FOUND8_{nm}_{lab}_{st}.npy',Bn); print('  FOUND!!',invariants(Bn),flush=True)
    print(f'{nm} ∩ {{{lab}}}: dimE(S)={dS} target {6+e}:',' '.join('%.0e'%r for r in res),f'({time.time()-t0:.0f}s)',flush=True)
