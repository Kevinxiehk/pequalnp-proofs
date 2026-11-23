import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/claude/work/L-gct-210/adversary')
import numpy as np
from level import Pk
exec(open('/home/claude/work/L-gct-210/adversary/red22lm2.py').read().split('def search')[0])
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
d=5
# LM for I: E3=0, GX=0
B=rng.normal(size=(d,7))+1j*rng.normal(size=(d,7)); xs=rng.normal(size=(80,d))+1j*rng.normal(size=(80,d))
def res(B):
    E3,GX=parts((xs@B).T); return np.concatenate([E3,GX])
lam=1e-3
for it in range(400):
    r=res(B); f=np.linalg.norm(r)
    J=np.zeros((len(r),B.size),complex); h=1e-7
    for k in range(B.size):
        Bp=B.copy().reshape(-1); Bp[k]+=h; J[:,k]=(res(Bp.reshape(B.shape))-r)/h
    H=J.conj().T@J; g=J.conj().T@r
    Bn=B+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-14),-g).reshape(B.shape); fn=np.linalg.norm(res(Bn))
    if fn<f: B=Bn; lam=max(lam/3,1e-14)
    else: lam*=4
    if f<1e-14 or lam>1e10: break
    B=B/np.linalg.norm(B,axis=1,keepdims=True)
print('I residual',np.linalg.norm(res(B)),'c sv',np.linalg.svd(B[:,5:],compute_uv=False))
one=np.ones(3)/3
a=np.array([1,-1,0.]); b=np.array([1,1,-2.]); b=b*(2/3)/(a@b) if a@b!=0 else None
# choose a,b in C^3_0 with a.b=2/3
a=np.array([1,-1,0.]); b=np.array([1/3,-1/3,0.])   # a.b = 2/3
assert abs(a@b-2/3)<1e-12
mats=[]
for v in B:
    Z11,Z12,Z21,s1,s2,c1,c2=v; Z22=-(Z11+Z12+Z21+s1+s2+c1+c2)
    t=np.zeros((5,5),complex); t[0,0]=Z11;t[0,1]=Z12;t[1,0]=Z21;t[1,1]=Z22
    t[0,2:]=s1*one; t[1,2:]=s2*one
    t[2:,0]=c1*one+c1*a; t[2:,1]=c2*one+c2*b
    mats.append(t)
for u in ([1,-1,0],[0,1,-1]):   # U_X: row 1 cols 3-5 sum-zero
    t=np.zeros((5,5),complex); t[0,2:]=u; mats.append(t)
# V_Y: column 1 rows 3-5 = v1 with v1 sum-zero, v1.b=0  (b^perp in C^3_0)
v1=np.array([1,1,-2.]); assert abs(v1@b)<1e-12
t=np.zeros((5,5),complex); t[2:,0]=v1; mats.append(t)
M=np.array(mats); print('dim',np.linalg.matrix_rank(M.reshape(len(M),-1),1e-9))
xr=rng.normal(size=(200,len(M)))+1j*rng.normal(size=(200,len(M))); xr/=np.linalg.norm(xr,axis=1,keepdims=True)
T=np.einsum('ri,iab->rab',xr,M); print('max |P_k| k=1..5 at 200 random unit points:',np.abs(Pk(T)[:,1:]).max(0))
np.save('/home/claude/work/L-gct-210/adversary/cand8.npy',M)
