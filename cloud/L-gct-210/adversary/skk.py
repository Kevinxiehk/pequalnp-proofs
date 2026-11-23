"""Sk x Sk-invariant level spaces (Sk permutes rows 0..k-1 and cols 0..k-1). Isotypic param:
L = W (triv, W in C^{(6-k)^2}) + std_row (x) U_r (U_r in C^{6-k}) + std_col (x) U_c + [std(x)std if s].
usage: skk.py k w0 ur uc s starts"""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from level import Pk
k=int(sys.argv[1]); m=5-k
def triv():
    out=[]
    T=np.zeros((5,5)); T[:k,:k]=1; out.append(T)
    for r in range(k,5): T=np.zeros((5,5)); T[r,:k]=1; out.append(T)
    for c in range(k,5): T=np.zeros((5,5)); T[:k,c]=1; out.append(T)
    for r in range(k,5):
        for c in range(k,5): T=np.zeros((5,5)); T[r,c]=1; out.append(T)
    return np.array(out)
A0=np.array([[1 if j==i else (-1 if j==i+1 else 0) for j in range(k)] for i in range(k-1)],float)
def stdrow(u):  # u in C^{1+m}: copies: block, then cols k..4
    out=[]
    for a in A0:
        T=np.zeros((5,5),complex); T[:k,:k]=u[0]*a[:,None]
        for c in range(m): T[:k,k+c]=u[1+c]*a
        out.append(T)
    return out
def stdstd():
    out=[]
    for a in A0:
        for b in A0:
            T=np.zeros((5,5)); T[:k,:k]=np.outer(a,b); out.append(T)
    return out
TR=triv(); nt=len(TR); nm=1+m
def grass(p,o,d,n,Q):
    if d==0: return np.zeros((0,n)),o
    X=p[o:o+d*(n-d)].reshape(d,n-d); return np.hstack([np.eye(d),X])@Q, o+d*(n-d)
def basis(p,w0,ur,uc,s,QS):
    out=[]; W,o=grass(p,0,w0,nt,QS['W']); out+=list(np.einsum('ik,kab->iab',W,TR))
    Ur,o=grass(p,o,ur,nm,QS['r']); Uc,o=grass(p,o,uc,nm,QS['c'])
    for u in Ur: out+=stdrow(u)
    for u in Uc: out+=[T.T for T in stdrow(u)]
    if s: out+=stdstd()
    return np.array(out)
def run(w0,ur,uc,s,starts,seed=0):
    rng=np.random.default_rng(seed); D=w0+(k-1)*(ur+uc)+(k-1)**2*s
    npar=w0*(nt-w0)+ur*(nm-ur)+uc*(nm-uc)
    xs=rng.normal(size=(300,D))+1j*rng.normal(size=(300,D)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    for st in range(starts):
        QS={}
        for key,n in (('W',nt),('r',nm),('c',nm)):
            Q,_=np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))); QS[key]=Q.T
        p=0.5*(rng.normal(size=npar)+1j*rng.normal(size=npar)); lam=1e-3
        res=lambda p: Pk(np.einsum('ri,iab->rab',xs,basis(p,w0,ur,uc,s,QS)))[:,1:].reshape(-1)
        for it in range(150):
            r=res(p); f=np.linalg.norm(r)
            if npar==0: break
            h=1e-7; J=np.array([(res(p+h*np.eye(npar)[q])-r)/h for q in range(npar)]).T
            H=J.conj().T@J; g=J.conj().T@r
            pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g); fn=np.linalg.norm(res(pn))
            if fn<f: p=pn; lam=max(lam/3,1e-12)
            else: lam*=4
            if fn<1e-11 or lam>1e9: break
        f=np.linalg.norm(res(p))
        print(f'  S{k}: (w0={w0};ur={ur},uc={uc};s={s}) dim {D} npar {npar} start {st}: res {f:.2e}',flush=True)
        if npar==0 or f<1e-9: break
run(*map(int,sys.argv[2:7]))
