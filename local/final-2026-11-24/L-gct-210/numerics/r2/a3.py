import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
which=sys.argv[1]; dels=[int(x) for x in sys.argv[2].split(',')]; e=int(sys.argv[3]); starts=int(sys.argv[4]); tl=float(sys.argv[5])
B={'ex1':ex1(),'ex2':ex2(),'ex3':ex3()}[which]
for i in dels:
    S=orth(np.delete(B,i,axis=0)); dS,ES,_=ext_space(S)
    rng=np.random.default_rng(100+i); res=[]
    t0=time.time()
    for st in range(starts):
        sB=np.einsum('ij,jab->iab',rng.normal(size=(e,dS))+1j*rng.normal(size=(e,dS)),ES)
        fc,Bn=lm_space(sB,6+e,fixed=S,ambient=ES,iters=200,tlimit=tl,rng=rng,rounds=4)
        res.append(fc)
        if fc<1e-10:
            print(f'  FOUND {which} drop{i} +{e}: fresh {fc:.1e}', invariants(Bn), 'angle to L %.1e'%angle(Bn[:7],B) ,flush=True)
            np.save(f'found_{which}_d{i}_e{e}_{st}.npy',Bn)
    print(f'{which} drop {i}: dimE(S)={dS}, target dim {6+e}: fresh per start',' '.join('%.0e'%r for r in res),f'({time.time()-t0:.0f}s)',flush=True)
