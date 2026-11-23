import numpy as np, itertools
n=5; rng=np.random.default_rng(3)
S3=list(itertools.permutations(range(3)))
def Pk3(t):
    s=0
    for R in itertools.combinations(range(n),3):
        for C in itertools.combinations(range(n),3):
            A=t[np.ix_(R,C)]; s+=sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]] for p in S3)
    return s
def Pk2(t):
    s=0
    for R in itertools.combinations(range(n),2):
        for C in itertools.combinations(range(n),2):
            A=t[np.ix_(R,C)]; s+=A[0,0]*A[1,1]+A[0,1]*A[1,0]
    return s
def rnd():
    a=rng.normal(size=n); a-=a.mean(); b=rng.normal(size=n); b-=b.mean()
    g=rng.normal(size=(n,n)); g-=g.mean(1,keepdims=True); g-=g.mean(0,keepdims=True)
    return a,b,g
rows=[];rhs=[];rows2=[];rhs2=[]
for _ in range(40):
    a,b,g=rnd(); t=a[:,None]+b[None,:]+g
    feats=[(g**3).sum(), (a*(g**2).sum(1)).sum(), (b*(g**2).sum(0)).sum(), (a[:,None]*b[None,:]*g).sum(), (a**3).sum(), (b**3).sum()]
    rows.append(feats); rhs.append(Pk3(t))
    rows2.append([(g**2).sum(),(a**2).sum(),(b**2).sum()]); rhs2.append(Pk2(t))
c,res,_,_=np.linalg.lstsq(np.array(rows),np.array(rhs),rcond=None)
print('P3 = %.6f p3(g) + %.6f sum a_i r_i(g) + %.6f sum b_j c_j(g) + %.6f sum a_i b_j g_ij + %.6f p3(a) + %.6f p3(b)'%tuple(c), ' resid',np.abs(np.array(rows)@c-rhs).max())
c2,_,_,_=np.linalg.lstsq(np.array(rows2),np.array(rhs2),rcond=None); print('P2 coeffs [p2 g, p2 a, p2 b]',np.round(c2,6),' resid',np.abs(np.array(rows2)@c2-rhs2).max())
