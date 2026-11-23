import numpy as np, sys; sys.path.insert(0,"/home/claude/work/L-gct-210/lemmaz")
from core import *
# A = C[y1..y5]/(y_j^2): arrays of length 32 indexed by bitmask
def mul(p,q):
    r=np.zeros(32,complex)
    for s in range(32):
        if p[s]==0: continue
        for t in range(32):
            if s&t==0 and q[t]!=0: r[s|t]+=p[s]*q[t]
    return r
def lin(a):
    p=np.zeros(32,complex)
    for j in range(5): p[1<<j]=a[j]
    return p
def pw(p,m):
    r=np.zeros(32,complex); r[0]=1
    for _ in range(m): r=mul(r,p)
    return r
rng=np.random.default_rng(5)
g=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); g-=g.mean(0)[None,:]   # columns sum to zero only
L=[lin(g[k]) for k in range(5)]
p2=sum(pw(l,2) for l in L); p3=sum(pw(l,3) for l in L)
e4=np.zeros(32,complex)
for e in range(5):
    pr=np.zeros(32,complex); pr[0]=1
    for k in range(5):
        if k!=e: pr=mul(pr,L[k])
    e4+=pr
M=minors(g)
err=0; err2=0
for e in range(5):
    pr=np.zeros(32,complex); pr[0]=1
    for k in range(5):
        if k!=e: pr=mul(pr,L[k])
    rhs=pw(L[e],4)-mul(p2/2,pw(L[e],2))-mul(p3/3,L[e])+e4
    err=max(err,np.abs(pr-rhs).max())
    err2=max(err2,max(abs(pr[31^(1<<j)]-M[e,j]) for j in range(5)))
print("identity prod_{k!=e} l_k = l_e^4 - (p2/2) l_e^2 - (p3/3) l_e + e4 (column-centred g): err",err," coefficient=minor err",err2)
