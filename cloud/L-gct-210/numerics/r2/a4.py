import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
which=sys.argv[1]; dels=[int(x) for x in sys.argv[2].split(',')]; starts=int(sys.argv[3]); tl=float(sys.argv[4])
B={'ex1':ex1(),'ex2':ex2(),'ex3':ex3()}[which]; L=orth(B)
for i in dels:
    S=orth(np.delete(B,i,axis=0)); dS,ES,_=ext_space(S)
    rng=np.random.default_rng(200+i); sols=[]; nfail=0
    for st in range(starts):
        sB=np.einsum('ij,jab->iab',rng.normal(size=(1,dS))+1j*rng.normal(size=(1,dS)),ES)
        fc,Bn=lm_space(sB,7,fixed=S,ambient=ES,iters=150,tlimit=tl,rng=rng,rounds=3)
        if fc<1e-10:
            if all(angle(Bn,s)>1e-5 for s in sols): sols.append(Bn)
        else: nfail+=1
    print(f'{which} drop {i}: dimE(S)={dS}; {starts} starts, {nfail} failed; distinct 7-dim level spaces ⊃ S: {len(sols)}',flush=True)
    for k,s in enumerate(sols):
        inv=invariants(s); dE,E,sv=ext_space(s)
        print(f'   sol{k}: angle to {which} {angle(s,L):.1e} (r,d,ra,rb)=({inv["r"]},{inv["d"]},{inv["ra"]},{inv["rb"]}) genrank {genrank(s)} dimE {dE} gap {sv[24-dE]:.1e}/{sv[25-dE]:.1e} fresh {fresh_check(s):.0e}',flush=True)
        np.save(f'sol7_{which}_d{i}_{k}.npy',s)
