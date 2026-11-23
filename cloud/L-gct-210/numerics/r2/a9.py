import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
B=ex1(); F=orth(B[2:])   # row 3 (4) + col 4 (1)
dF,EF,sF=ext_space(F); print('F = row3+col4 (dim 5): dimE(F)=',dF,'gap %.1e/%.1e'%(sF[24-dF],sF[25-dF]))
blk=[]
for i in range(3):
    for j in range(4):
        M=np.zeros((5,5),complex); M[i,j]=1; blk.append(M)
blk=np.array(blk)
# E(F) cap block?
Em=EF.reshape(dF,-1); Bm=blk.reshape(12,-1)
M=np.vstack([Em,-Bm]).T; u,sv,vh=np.linalg.svd(M); k=np.sum(sv>1e-9*sv[0]); ns=vh[k:].conj()
print('dim E(F) ∩ block(3x4) =',len(ns))
e=int(sys.argv[1]); starts=int(sys.argv[2]); amb=sys.argv[3]
A=EF if amb=='E' else blk
rng=np.random.default_rng(e); sols=[]
for st in range(starts):
    sB=np.einsum('ij,jab->iab',rng.normal(size=(e,len(A)))+1j*rng.normal(size=(e,len(A))),A)
    fc,Bn=lm_space(sB,5+e,fixed=F,ambient=A,iters=150,tlimit=12,rng=rng,rounds=3)
    msg=f' st{st}: fresh {fc:.0e}'
    if fc<1e-9:
        inv=invariants(Bn); msg+=f' (r,d,ra,rb)=({inv["r"]},{inv["d"]},{inv["ra"]},{inv["rb"]}) equiv-angle to ex1/ex2/ex3: '+' '.join('%.0e'%equiv_angle_c(Bn,X) for X in (ex1(),ex2(),ex3()))
        np.save(f'F_e{e}_{amb}_{st}.npy',Bn)
    print(msg,flush=True)
