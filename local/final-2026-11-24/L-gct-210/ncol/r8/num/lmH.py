# numerical probe for the last piece of case (C): H = ker c (+) e_0 U_0 (6-dim) with U_0 of a fixed type, C = U_0 + C t'' (t'' free),
# ker c inside V_0' = {Y : c(Y) = 0, row 0 = -s, s in U_0^perp}.  Residual: R(Y) - proj_C R(Y) for Y in H at random points; Gram(ker c) = I.
# usage: python3 -I lmH.py TYPE(a3|b22|b23) SEED NSTARTS [DIMK=4]
import numpy as np, itertools, sys
typ=sys.argv[1]; seed=int(sys.argv[2]); nst=int(sys.argv[3]); DK=int(sys.argv[4]) if len(sys.argv)>4 else 4
rng=np.random.default_rng(seed); w3=np.exp(2j*np.pi/3)
if typ=='a3': U=np.array([[1,-1,0,0,0],[0,1,-1,0,0]],complex)
elif typ=='b22': U=np.array([[1,-1,0,0,0],[0,0,1,-1,0]],complex)
else: U=np.array([[1,-1,0,0,0],[0,0,1,w3,w3*w3]],complex)     # b23 with a generic-ish v in V_234
# U_0^perp (bilinear) basis
_,_,vh=np.linalg.svd(U); Dp=vh[2:].conj()            # rows d with U d = 0 ... use null space of U (bilinear: U @ d = 0)
ns=np.linalg.svd(U)[2][2:]; Dp=np.array([v.conj() for v in ns]); assert np.allclose(U@Dp.T,0,atol=1e-12)
n1=np.array([1,w3,w3*w3]); n2=np.array([1,w3*w3,w3])
# basis of V_0': s in span(Dp) (3), a (5), b (5)
Bas=[]
for d in Dp:
    Y=np.zeros((4,5),complex); Y[0]=-d; Y[1:]=d/3; Bas.append(Y)
for nu in (n1,n2):
    for j in range(5):
        Y=np.zeros((4,5),complex); Y[1:,j]=nu; Bas.append(Y)
Bas=np.array(Bas); NB=len(Bas)
perms=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in perms)
def R(Y): JY=1+Y; return np.array([perm4(np.delete(JY,k,axis=1))-24 for k in range(5)])
NS=int(__import__("os").environ.get("NS","80")); pts=[(rng.normal(size=DK)+1j*rng.normal(size=DK), rng.normal(size=2)+1j*rng.normal(size=2)) for _ in range(NS)]
nv=2*(DK*NB+5)
def unpack(x):
    z=x[:nv//2]+1j*x[nv//2:]; return z[:DK*NB].reshape(DK,NB), z[DK*NB:]
def resid(x):
    Kc,t=unpack(x); KB=np.tensordot(Kc,Bas,axes=(1,0)); Cb=np.vstack([U,t[None,:]])
    out=[]
    for ck,cu in pts:
        Y=np.tensordot(ck,KB,axes=(0,0)); Y=Y.copy(); Y[0]+=cu@U
        r=R(Y); c,*_=np.linalg.lstsq(Cb.T,r,rcond=None); out+=list(r-Cb.T@c)
    out+=list((Kc@Kc.conj().T-np.eye(DK)).ravel()); out.append(t.sum()); out+=list(U.conj()@t); out.append(t@t.conj()-1)
    out=np.array(out); return np.concatenate([out.real,out.imag])
def jac(x,f0,h=1e-7):
    J=np.zeros((len(f0),len(x)))
    for i in range(len(x)):
        xp=x.copy(); xp[i]+=h; J[:,i]=(resid(xp)-f0)/h
    return J
best=[]
for st in range(nst):
    x=rng.normal(size=nv)*0.5; lam=1e-2; f=resid(x); c=f@f
    for it in range(120):
        J=jac(x,f); g=J.T@f; Hm=J.T@J
        while True:
            dx=np.linalg.solve(Hm+lam*np.diag(np.diag(Hm)+1e-12),-g); xn=x+dx; fn=resid(xn); cn=fn@fn
            if cn<c: x,f,c=xn,fn,cn; lam=max(lam/3,1e-12); break
            lam*=4
            if lam>1e8: break
        if lam>1e8 or c<1e-24: break
    best.append(c); print('%s DK=%d start %d: residual %.3e (%d its)'%(typ,DK,st,c,it),flush=True)
    if c<1e-20: np.save('H_%s_d%d_s%d_%d.npy'%(typ,DK,seed,st),x)
print('min',min(best))
