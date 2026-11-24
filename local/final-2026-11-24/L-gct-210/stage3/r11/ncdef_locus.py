# dim T_1(N(w2,w3)) on structured sub-families, to locate where T_1 jumps (generic 10, stored member 13).
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2'); import fo2lib as F
rg=np.random.default_rng(3); J=np.ones((5,5))
def member(w2,w3):
    B=[]
    for (i,k) in ((0,1),(1,2),(2,3)):
        M=np.zeros((5,5),complex); M[i,0]=1; M[k,0]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[2]=w2; B.append(M); M=np.zeros((5,5),complex); M[3]=w3; B.append(M); return np.array(B)
def T1dim(B):
    d=len(B); A=np.array([F.cof(J+np.tensordot(rg.normal(size=d)+1j*rg.normal(size=d),B,axes=1)) for _ in range(120)])
    s=np.linalg.svd(A,compute_uv=False); r=int((s>1e-8*s[0]).sum()); return 25-r, s[r-1]/s[0]
def orth(w2,b):   # vector in V0 orthogonal to w2 (bilinear), from b
    A=np.array([np.r_[1,np.zeros(4)],np.ones(5),w2]); ns=np.linalg.svd(A)[2][3:].conj(); return ns.T@(ns.conj()@b)
def r5(): return rg.normal(size=5)+1j*rg.normal(size=5)
def v0(x): x=x.copy(); x[0]=0; x[1:]-=x[1:].mean(); return x
cases={}
cases['generic']=lambda: (lambda w2:(w2,orth(w2,r5())))(v0(r5()))
cases['w2 = e4-e1']=lambda: (lambda w2:(w2,orth(w2,r5())))(np.array([0,-1,0,0,1],complex))
cases['w2 isotropic']=lambda: (lambda w2:(w2,orth(w2,r5())))(np.array([0,1,np.exp(2j*np.pi/3),np.exp(4j*np.pi/3),0],complex)*1)
cases['w2 3-col (0,1,-2,1,0)']=lambda: (lambda w2:(w2,orth(w2,r5())))(np.array([0,1,-2,1,0],complex))
cases['w2,w3 two-col disjoint']=lambda: (np.array([0,1,-1,0,0],complex),np.array([0,0,0,1,-1],complex))
cases['w2 two-col, w3 on 3 cols']=lambda: (np.array([0,1,-1,0,0],complex),np.array([0,1,1,-2,0],complex))
cases['w2 = w3 isotropic']=lambda: (np.array([0,1,np.exp(2j*np.pi/3),np.exp(4j*np.pi/3),0]),)*2
cases['w2 two-col, w3 = (0,1,1,a,b)']=lambda: (lambda a: (np.array([0,1,-1,0,0],complex),np.array([0,1,1,a,-2-a],complex)))(rg.normal()+1j*rg.normal())
for k,f in cases.items():
    out=[]
    for _ in range(3):
        w2,w3=f(); B=member(np.asarray(w2,complex),np.asarray(w3,complex))
        lev=max(abs(F.perm_small(J+np.tensordot(rg.normal(size=5)+1j*rg.normal(size=5),B,axes=1))-120) for _ in range(5))
        t=T1dim(B); out.append('%d (lev %.0e)'%(t[0],lev))
    print('%-32s dim T_1: %s'%(k,', '.join(out)))
