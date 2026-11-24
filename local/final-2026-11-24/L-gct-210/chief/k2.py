import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
from core import *
from testAB_lib import hat, rank, sub_with_zero
pairs=list(itertools.combinations(range(5),2))
def pol2(u,v,S,T):
    (i,k),(j,l)=S,T
    return u[i,j]*v[k,l]+u[k,l]*v[i,j]+u[i,l]*v[k,j]+u[k,j]*v[i,l]
def K2(Bh):
    m=len(Bh); idx=[(a,b) for a in range(m) for b in range(a,m)]
    Psi=np.array([[pol2(Bh[a],Bh[b],S,T) for (a,b) in idx] for S in pairs for T in pairs])
    N=nullspace(Psi); return idx,N
def line_span(B):
    # single-row and single-column elements of L (coefficient vectors)
    fam=[]
    for r in range(5):
        cells=[(i,j) for i in range(5) for j in range(5) if i!=r]
        fam.append(('row%d'%r,sub_with_zero(B,cells)))
    for c in range(5):
        cells=[(i,j) for i in range(5) for j in range(5) if j!=c]
        fam.append(('col%d'%c,sub_with_zero(B,cells)))
    return fam
for name,f in SP.items():
    B=f(); Bh=hat(B); m=len(Bh); idx,N=K2(Bh)
    fam=line_span(B)
    # build tensors (as vectors over idx) for products within each family
    vecs=[]
    pos={p:k for k,p in enumerate(idx)}
    def sym(ca,cb):
        v=np.zeros(len(idx),complex)
        for a in range(m):
            for b in range(m):
                p=(a,b) if a<=b else (b,a); v[pos[p]]+=ca[a]*cb[b]*(1 if a==b else 0.5)
        return v
    for nm,F in fam:
        k=F.shape[1]
        for a in range(k):
            for b in range(a,k):
                ca=np.concatenate([[0],F[:,a]]); cb=np.concatenate([[0],F[:,b]])
                vecs.append(sym(ca,cb))
    dl=rank(np.array(vecs)) if vecs else 0
    # is span(vecs) inside K2 and what is the excess
    tot=rank(np.concatenate([N.T,np.array(vecs)])) if vecs else N.shape[1]
    print('%-12s K2=%d  line-products span=%d  (K2 + line)=%d  line dims:'%(name,N.shape[1],dl,tot),[(nm,F.shape[1]) for nm,F in fam if F.shape[1]])
