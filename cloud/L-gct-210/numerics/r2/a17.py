import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
F0=orth(ex1()[2:6])  # row 3 sum-zero, 4-dim
dF,EF,_=ext_space(F0); print('row3 (dim4): dimE =',dF,flush=True)
rng=np.random.default_rng(int(sys.argv[1])); e=int(sys.argv[2])
for st in range(int(sys.argv[3])):
    sB=np.einsum('ij,jab->iab',rng.normal(size=(e,dF))+1j*rng.normal(size=(e,dF)),EF)
    fc,Bn=lm_space(sB,4+e,fixed=F0,ambient=EF,iters=150,tlimit=float(sys.argv[4]),rng=rng,rounds=3)
    msg=f' st{st} target {4+e}: fresh {fc:.0e}'
    if fc<1e-10:
        inv,dE,gap,gr=inv_full(Bn)
        msg+=f' (r,d,ra,rb)=({inv["r"]},{inv["d"]},{inv["ra"]},{inv["rb"]}) rk{gr} dimE {dE} gap {gap[0]:.0e}/{gap[1]:.0e}'
        if 4+e==7: msg+=' equiv to fam/ex1/ex2/L080: '+' '.join('%.0e'%equiv_angle_c(Bn,X) for X in (fam(0.3+0.7j),ex1(),ex2(),L080()))
        np.save(f'row3_e{e}_{sys.argv[1]}_{st}.npy',Bn)
    print(msg,flush=True)
