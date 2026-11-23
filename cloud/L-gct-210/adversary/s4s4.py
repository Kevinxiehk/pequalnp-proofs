"""S4xS4-invariant (rows1-4, cols1-4 permuted) subspaces: L = W (trivial, W in C^4) + std_row (x) U_r + std_col (x) U_c.
LM over the small parameters (W, U_r, U_c). usage: s4s4.py w0 ur uc starts"""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from level import Pk
def triv():
    T=np.zeros((4,5,5)); T[0,:4,:4]=1; T[1,4,:4]=1; T[2,:4,4]=1; T[3,4,4]=1; return T
A0=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1.]])  # basis of C^4_0
def stdrow(u):  # 3 matrices
    out=[]
    for a in A0:
        T=np.zeros((5,5),complex); T[:4,:4]=u[0]*a[:,None]; T[:4,4]=u[1]*a; out.append(T)
    return out
def stdcol(u):
    return [T.T for T in stdrow(u)]
QS={}
def basis(p,w0,ur,uc):
    o=0; out=[]
    if w0:
        X=p[o:o+w0*(4-w0)].reshape(w0,4-w0); o+=w0*(4-w0); W=np.hstack([np.eye(w0),X])@QS['W']
        out+=list(np.einsum('ik,kab->iab',W,triv()))
    if ur==2: out+=stdrow([1,0])+stdrow([0,1])
    elif ur==1: out+=stdrow(np.array([1,p[o]])@QS['r']); o+=1
    if uc==2: out+=stdcol([1,0])+stdcol([0,1])
    elif uc==1: out+=stdcol(np.array([1,p[o]])@QS['c']); o+=1
    return np.array(out)
def resid(p,w0,ur,uc,xs):
    B=basis(p,w0,ur,uc); T=np.einsum('ri,iab->rab',xs,B); return Pk(T)[:,1:].reshape(-1)
def run(w0,ur,uc,starts,seed=0):
    rng=np.random.default_rng(seed); D=w0+3*ur+3*uc; npar=w0*(4-w0)+(ur==1)+(uc==1)
    xs=rng.normal(size=(200,D))+1j*rng.normal(size=(200,D)); xs/=np.linalg.norm(xs,axis=1,keepdims=True); best=np.inf
    for s in range(starts):
        for k,m in (('W',4),('r',2),('c',2)):
            Q,_=np.linalg.qr(rng.normal(size=(m,m))+1j*rng.normal(size=(m,m))); QS[k]=Q.T
        p=rng.normal(size=npar)+1j*rng.normal(size=npar); lam=1e-3
        if npar==0:
            r=resid(p,w0,ur,uc,xs); print(f'  ({w0};{ur},{uc}) dim {D}: fixed space res {np.linalg.norm(r):.2e}'); return
        def nres(p):
            B=basis(p,w0,ur,uc).reshape(D,-1); sv=np.linalg.svd(B,compute_uv=False)
            r=resid(p,w0,ur,uc,xs); return r, sv[-1]/sv[0]
        for it in range(200):
            r,_=nres(p); f=np.linalg.norm(r); h=1e-7
            J=np.array([(nres(p+h*np.eye(npar)[k])[0]-r)/h for k in range(npar)]).T
            H=J.conj().T@J; g=J.conj().T@r
            pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g); fn=np.linalg.norm(nres(pn)[0])
            if fn<f: p=pn; lam=max(lam/3,1e-12)
            else: lam*=4
            if fn<1e-11 or lam>1e9: break
        r,cond=nres(p); f=np.linalg.norm(r); best=min(best,f)
        print(f'  ({w0};{ur},{uc}) dim {D} s{s}: res {f:.2e} basis-cond {cond:.2e}',flush=True)
    return best
if __name__=='__main__':
    w0,ur,uc,st=map(int,sys.argv[1:5]); run(w0,ur,uc,st)
