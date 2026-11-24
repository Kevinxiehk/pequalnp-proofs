import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
rng=np.random.default_rng(int(sys.argv[1]))
seeds=[('L080',L080()),('ex1',ex1()),('ex2',ex2()),('ex3',ex3()),('fam',fam(0.3+0.7j)),('lim0',lim0())]
for nm,B in seeds[int(sys.argv[2]):int(sys.argv[3])]:
    dE,E,_=ext_space(B)
    for pert in [0.05,0.3]:
        sB=E+pert*(rng.normal(size=E.shape)+1j*rng.normal(size=E.shape))
        t0=time.time()
        fc,Bn=lm_space(sB,8,ambient=sumzero_ambient(),iters=120,tlimit=22,rng=rng,rounds=3)
        print(f'{nm}: global 8-dim LM from E(L)+{pert} noise: fresh {fc:.1e} ({time.time()-t0:.0f}s)',flush=True)
        if fc<1e-10: np.save(f'FOUND8_global_{nm}.npy',Bn); print('  FOUND',invariants(Bn))
