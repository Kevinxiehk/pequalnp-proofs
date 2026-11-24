import numpy as np, sys, itertools; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/lemmaz")
from core import *
rng=np.random.default_rng(3)
def randDC():
    g=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); g-=g.mean(0)[None,:]; g-=g.mean(1)[:,None]; return g
def pij(g,j,v): return np.prod(np.delete(v,j))
# (C) general identity on random DC g: Walsh-4 coefficient vs minor
g=randDC(); M=minors(g); rat=[]
for e in range(5):
    for j in range(5):
        r=g
        w=pij(g,j,r[e])-sum(pij(g,j,r[k]) for k in range(5) if k!=e)+sum(pij(g,j,r[k]+r[l]) for k in range(5) for l in range(k+1,5) if e not in (k,l))-sum(pij(g,j,r[e]+r[k]) for k in range(5) if k!=e)
        rat.append(w/M[e,j])
rat=np.array(rat); print("(C) Walsh coefficient / minor: const?",rat[0],"spread %.1e"%np.abs(rat-rat[0]).max())
# (I) on random row-centred g
g=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); g-=g.mean(1)[:,None]; M=minors(g); R=g@g.T; err=0
for e in range(5):
    S=[k for k in range(5) if k!=e]
    for n in range(5):
        lhs=12*np.prod(g[S,n]); rhs=0
        for (k,k2) in itertools.combinations(S,2):
            m,m2=[q for q in S if q not in (k,k2)]; rhs+=R[k,k2]*g[m,n]*g[m2,n]
        for m in S:
            a,b,c=[q for q in S if q!=m]; rhs+=np.sum(g[a]*g[b]*g[c])*g[m,n]
        rhs-= (M[e].sum()-M[e,n])/2
        err=max(err,abs(lhs-rhs))
print("(I) Hadamard form identity on random row-centred g: err %.1e"%err)
# special DC solution with zero row 4 (4x5 DC, sliced)
def dc45(x):
    c=x.reshape(3,4); g=np.zeros((5,5),complex); g[:3,:4]=c; g[:3,4]=-c.sum(1); g[3,:]=-g[:3].sum(0); return g
lam=rng.normal(size=(7,12))+1j*rng.normal(size=(7,12)); rhs0=rng.normal(size=7)+1j*rng.normal(size=7)
x,res=solve(lambda x: np.concatenate([minors(dc45(x))[4],lam@x-rhs0]),rng.normal(size=12)+1j*rng.normal(size=12))
g=dc45(x); print("special DC solution: res %.1e max|minor| %.1e"%(res,np.abs(minors(g)).max()))
R=g@g.T; G=g.T@g
e1=max(abs(sum(pij(g,j,g[e]+g[k]) for k in range(5) if k!=e)-pij(g,j,g[e])-sum(pij(g,j,g[k]) for k in range(5))) for e in range(5) for j in range(5))
print("(C) simplified form on solution: err %.1e"%e1)
e2=max(abs(6*np.sum(g[a]*g[b]*g[c]*g[d])-(R[a,b]*R[c,d]+R[a,c]*R[b,d]+R[a,d]*R[b,c])) for a,b,c,d in itertools.combinations(range(5),4))
print("(S4) 6 sum abcd = RR+RR+RR on solution: err %.1e"%e2)
p2=np.sum(g*g); r=np.diag(R); c=np.diag(G); T=(g**3).sum(0); R2=R@R
e3=max(abs(36*np.sum(g[a]**4)-18*np.sum(g[a]**2*c)-12*np.sum(g[a]*T)+3*r[a]*p2+6*R2[a,a]-18*r[a]**2+6*np.sum(R[a]*r)) for a in range(5))
print("(P4r) row-refined P_4 on solution: err %.1e"%e3)
# (L): abc(a+b+c) top coefficients = perm sums on each 4 columns, on solution
e4=0
for a,b,c in itertools.combinations(range(5),3):
    for U in itertools.combinations(range(5),4):
        U=list(U); A=g[a,U];B=g[b,U];C=g[c,U]
        v=perm(np.array([A,A,B,C]))+perm(np.array([A,B,B,C]))+perm(np.array([A,B,C,C])); e4=max(e4,abs(v))
print("(L) local form on solution: err %.1e"%e4)
# rank-2 lemma sanity and Z_4 pair claim: t=(w,w,w^2,w^2): e1+e2 on triples
w=np.exp(2j*np.pi/3); t=np.array([w,w,w**2,w**2])
print("(Z_4) e1+e2 on triples for (w,w,w2,w2):",max(abs(sum(t[list(U)])+sum(t[i]*t[k] for i,k in itertools.combinations(U,2))) for U in itertools.combinations(range(4),3)))
