import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
F0=orth(ex1()[2:6])
blk=[]
for i in [0,1,2,4]:
    for j in [2,4]:
        M=np.zeros((5,5),complex); M[i,j]=1; blk.append(M)
blk=np.array(blk)
rng=np.random.default_rng(9)
for e in [3,4]:
    res=[]
    for st in range(int(sys.argv[1])):
        sB=np.einsum('ij,jab->iab',rng.normal(size=(e,8))+1j*rng.normal(size=(e,8)),blk)
        fc,Bn=lm_space(sB,4+e,fixed=F0,ambient=blk,iters=150,tlimit=10,rng=rng,rounds=3)
        res.append(fc)
        if fc<1e-10 and e==3 and st<3:
            B2=Bn; dE,E,s=ext_space(B2); print(f'   e=3 sol: dimE {dE} sv {s[16:19]} E level? {fresh_check(E):.1e}',flush=True)
        if fc<1e-10 and e==4: np.save(f'FOUND8_row3blk_{st}.npy',Bn); print('  FOUND 8!',invariants(Bn))
    print(f'row3 + {e} vectors in 4x2 block (rows 0,1,2,4 x cols 2,4): fresh per start',' '.join('%.0e'%r for r in res),flush=True)
