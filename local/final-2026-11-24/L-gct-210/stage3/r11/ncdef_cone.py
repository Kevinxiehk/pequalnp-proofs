# Round 11: on a member N of the jump locus H, the common null cone K = {v in V = T_1/N : q_m(v) = 0 for all m in N} (projective, P^7).
# A 9-dim level L containing N needs a P^3 inside K (4-dim common isotropic subspace); an 8-dim one a P^2. Calibration: L(N)/N (P^1) lies in K.
# usage: python3 -I ncdef_cone.py SEED NSTARTS [stored]
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2'); import fo2lib as F
exec(open('/home/kevxhk/work/L-gct-210/stage3/r11/ncdef_hyper.py').read().split('for _ in range(4):')[0])
seed,NS=int(sys.argv[1]),int(sys.argv[2]); rg=np.random.default_rng(seed)
if len(sys.argv)>3:
    Z=np.load('/home/kevxhk/work/L-gct-210/rows/ncdef_d5_e2_k1_s1.npy'); B=np.zeros((5,5,5),complex); B[:,:4,:]=Z
else:
    w2,w3=hyper_member(); B=member(w2,w3)
d=len(B)
def pt(): return J+np.tensordot(rg.normal(size=d)+1j*rg.normal(size=d),B,axes=1)
A=np.array([F.cof(pt()) for _ in range(160)]); Nb,s=F.null(A); n=Nb.shape[1]
Bv=B.reshape(d,25).T; X=np.linalg.lstsq(Nb,Bv,rcond=None)[0]
# complement of N inside T_1, orthonormal for the Hermitian product in T_1-coordinates
Q=np.linalg.qr(np.concatenate([X,rg.normal(size=(n,n-d))+1j*rg.normal(size=(n,n-d))],1))[0]; Vb=Nb@Q[:,d:]; m=n-d
GV=[Vb.T@F.hess(pt())@Vb for _ in range(3*m*(m+1)//2)]
iu=np.triu_indices(m); Mx=np.array([g[iu] for g in GV]); u_,sv,vh=np.linalg.svd(Mx); k=int((sv>1e-8*sv[0]).sum())
Gs=[]
for row in vh[:k]:                                            # basis of the span of the forms (rows of vh, NO conjugation)
    S=np.zeros((m,m),complex); S[iu]=row; S=S+S.T-np.diag(np.diag(S)); Gs.append(S)
print('dim T_1 = %d, dim V = %d, forms span dim %d'%(n,m,k),flush=True)
# calibration: the lift L(N) = N + e_4 (x) (C(N)+C1)^perp ; its image in V must be isotropic for all forms
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); import build7
Lift,e=build7.build(B[:,:4,:]); Lv=Lift.reshape(len(Lift),25).T
Ly=np.linalg.lstsq(Vb,Lv-Bv@np.linalg.lstsq(Bv,Lv,rcond=None)[0],rcond=None)[0]   # V-coordinates of the lift mod N (approx.)
_u,_s,_v=np.linalg.svd(Ly); LyQ=_u[:,:int((_s>1e-8*_s[0]).sum())]          # column space by SVD (QR picks noise on rank-deficient Ly)
print('lift: dim %d, defect %d; image in V has dim %d; max |form| on it: %.1e'%(len(Lift),e,LyQ.shape[1],max(np.abs(LyQ.T@G@LyQ).max() for G in Gs)),flush=True)
r0=rg.normal(size=m)+1j*rg.normal(size=m)
def Fv(v): return np.concatenate([[v@G@v for G in Gs],[r0@v-1]])
def Jv(v): return np.array([2*(G@v) for G in Gs]+[r0])
sols=[]
for st in range(NS):
    v=rg.normal(size=m)+1j*rg.normal(size=m); lam=1e-3
    f=Fv(v); nf=np.linalg.norm(f)
    for it in range(300):
        Jm=Jv(v); A_=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dv=np.linalg.solve(A_+lam*np.eye(m),g); f2=Fv(v-dv); n2=np.linalg.norm(f2)
            if n2<nf: v=v-dv; f,nf=f2,n2; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok or nf<1e-13: break
    if nf<1e-10:
        Jm=Jv(v)[:-1]; rkJ=np.linalg.matrix_rank(Jm,1e-7*np.abs(Jm).max())
        inlift=np.linalg.norm(v/np.linalg.norm(v)-LyQ@(LyQ.conj().T@(v/np.linalg.norm(v))))
        sols.append((rkJ,inlift)); print('start %d: point of K, Jacobian rank %d -> local projective dim of K <= %d ; distance to lift-plane %.1e'%(st,rkJ,m-1-rkJ,inlift),flush=True)
    else: print('start %d: res %.1e'%(st,nf),flush=True)
