# numerical (LM) search for TWO-ZERO split isotropic (5,1) spaces: L' = C e_0 m^T (+) L'', m = (1,w,w^2,0,0), L'' 4-dim in U2
# (row 0 = -(alpha 1 + delta e_3 + delta' e_4), all column sums 0).  Residuals: R_3, R_4, m_l R_k - m_k R_l (k<l<=2) at NS random
# points (u, kappa) + Gram(L'') = I (keeps rank 4).  usage: python3 -I lm2z.py SEED NSTARTS DIM(4, or 3 for calibration)
import numpy as np, itertools, sys
seed=int(sys.argv[1]); nst=int(sys.argv[2]); D=int(sys.argv[3]) if len(sys.argv)>3 else 4
rng=np.random.default_rng(seed); w=np.exp(2j*np.pi/3); m=np.array([1,w,w*w,0,0])
# basis of U2 as 4x5 matrices (13 of them)
def U2basis():
    B=[]
    for kind in range(3):          # alpha, delta, delta'
        Y=np.zeros((4,5),complex); r0=np.zeros(5,complex)
        if kind==0: r0[:]=-1
        elif kind==1: r0[3]=-1
        else: r0[4]=-1
        Y[0]=r0; Y[1:]=-r0/3; B.append(Y)
    nu1=np.array([1,w,w*w]); nu2=np.array([1,w*w,w])
    for nu in (nu1,nu2):
        for j in range(5):
            Y=np.zeros((4,5),complex); Y[1:,j]=nu; B.append(Y)
    return np.array(B)
UB=U2basis()
perms=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in perms)
def Rvec(Y):
    JY=1+Y; return np.array([perm4(np.delete(JY,k,axis=1))-24 for k in range(5)])
E0=np.zeros((4,5),complex); E0[0]=m
NS=24; pts=[(rng.normal(size=D)+1j*rng.normal(size=D), rng.normal()+1j*rng.normal()) for _ in range(NS)]
def resid(x):
    C=(x[:D*13]+1j*x[D*13:]).reshape(D,13)
    V=np.tensordot(C,UB,axes=(1,0))       # D x 4 x 5
    out=[]
    for u,kk in pts:
        Y=np.tensordot(u,V,axes=(0,0))+kk*E0
        R=Rvec(Y)
        out+= [R[3],R[4]]+[m[l]*R[k]-m[k]*R[l] for k in range(3) for l in range(k+1,3)]
    G=C@C.conj().T-np.eye(D); out+=list(G.ravel())
    out=np.array(out); return np.concatenate([out.real,out.imag])
def jac(x,f0,h=1e-7):
    J=np.zeros((len(f0),len(x)))
    for i in range(len(x)):
        xp=x.copy(); xp[i]+=h; J[:,i]=(resid(xp)-f0)/h
    return J
best=[]
for st in range(nst):
    x=rng.normal(size=2*D*13)*0.5; lam=1e-2
    f=resid(x); c=f@f
    for it in range(150):
        J=jac(x,f); g=J.T@f; H=J.T@J
        while True:
            dx=np.linalg.solve(H+lam*np.diag(np.diag(H)+1e-12),-g); xn=x+dx; fn=resid(xn); cn=fn@fn
            if cn<c: x,f,c=xn,fn,cn; lam=max(lam/3,1e-12); break
            lam*=4
            if lam>1e8: break
        if lam>1e8 or c<1e-26: break
    best.append(c); print('start %d: residual %.3e after %d its'%(st,c,it),flush=True)
print('min residual',min(best))
