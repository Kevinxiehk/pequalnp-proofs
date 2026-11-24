# Round 11: numerical probe of the (5,1) question of Lemma PFC: 4x5 level spaces of dim D whose deletion vectors p_k(Y) all lie in the FIXED
# line C m (m = (1,1,1,1,-4) for the target). rows/clm.py defect mode with e = 1 and T fixed to 0 (first basis vector of 1^perp = m/|m|).
# usage: python3 -I m0_search.py MODE D SEED NSTARTS     MODE = m0 (target) | cal (m = defect line of a known (4,1) space, D = 4)
import sys, glob, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff')
import clm, oracle
mode,D,seed,NS=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
if mode=='m0': m=np.array([1,1,1,1,-4],complex)
else:
    Z=np.load(sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d4_defect1_s*.npy'))[seed%10]); s=clm.defect_dim(Z)
    rg0=np.random.default_rng(8); A=rg0.normal(size=(80,len(Z)))+1j*rg0.normal(size=(80,len(Z))); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=clm.G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,clm.Rdel()).reshape(-1,5)
    u,sv,vh=np.linalg.svd(pk); m=vh[0]            # dominant direction = defect line (row space of pk)
    print('calibration defect line from known (4,1): singular values',np.round(sv[:3]/sv[0],8),flush=True)
mn=m/np.linalg.norm(m)
Bq=np.linalg.qr(np.concatenate([mn[:,None],np.random.default_rng(1).normal(size=(5,3))+0j,np.ones((5,1))],1))[0]
Fb=Bq[:,:4].T                                       # rows: mn and three more, all orthonormal; then orthogonalise against 1 below
one=np.ones(5)/np.sqrt(5); Fb=Fb-np.outer(Fb@one.conj(),one); 
Q,_=np.linalg.qr(Fb.T); Fb=Q.T                      # orthonormal basis of 1^perp with first vector ~ mn (mn is in 1^perp up to phase)
Fb[0]=mn if abs(mn.sum())<1e-12 else Fb[0]
Q,_=np.linalg.qr(Fb.T); Fb=Q.T
class W:
    def __init__(s,P): s.P=P; s.rng=P.rng; s.nvar=P.nW
    def fun(s,z,jac=True):
        zf=np.concatenate([z,np.zeros(s.P.nT,complex)])
        if jac:
            r,J=s.P.fun(zf); return r,J[:,:s.P.nW]
        return s.P.fun(zf,jac=False)
hits=0; res=[]
for st in range(NS):
    P=clm.Problem(4,D,'defect',e=1,seed=1000*seed+st,N=300); P.Fb=Fb; P.Fd=Fb.conj()
    z,c=clm.solve(W(P),iters=300); res.append(c); info=''
    if c<1e-8:
        Zs=P.basis(np.concatenate([z,np.zeros(P.nT)])); sv=clm.defect_dim(Zs); lev=clm.fresh_level(Zs)
        info='  HIT: fresh level %.1e, deletion-vector singular values %s, rank %d'%(lev,np.round(sv[:3]/sv[0],8),np.linalg.matrix_rank(Zs.reshape(D,-1),1e-7))
        hits+=1; np.save('/home/kevxhk/work/L-gct-210/stage3/r11/m0hit_%s_%d_%d_%d.npy'%(mode,D,seed,st),Zs)
    print('start %d res %.2e%s'%(st,c,info),flush=True)
print('MODE %s D %d: %d hits in %d starts; residual quantiles %s'%(mode,D,hits,NS,np.round(np.quantile(res,[0,.25,.5]),8)),flush=True)
