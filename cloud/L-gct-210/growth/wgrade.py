# max P2P3 weight spaces in full sum-zero U under gradings by <sigma> x <tau> (rows, cols)
import numpy as np, itertools, sys
sys.path.insert(0,'.')
from core import *
reps={'1':[0,1,2,3,4],'(01)':[1,0,2,3,4],'(01)(23)':[1,0,3,2,4],'(012)':[1,2,0,3,4],'(012)(34)':[1,2,0,4,3],'(0123)':[1,2,3,0,4],'(01234)':[1,2,3,4,0]}
def order(p):
    q=list(range(5)); k=0
    while True:
        q=[p[x] for x in q]; k+=1
        if q==list(range(5)): return k
def eig_dims(s,t):
    a,b=order(s),order(t)
    # action on 5x5: (g u)[s[i],t[j]] = u[i,j]
    def act(Um):
        Um=Um.reshape(5,5); V=np.zeros_like(Um)
        for i in range(5):
            for j in range(5): V[s[i],t[j]]=Um[i,j]
        return V.ravel()
    dims={}
    # projector onto character (x,y): (1/ab) sum_{k,m} zeta_a^{-xk} zeta_b^{-ym} sigma^k tau^m
    # build sigma-action matrix and tau-action matrix on UB coords
    def mat(f): return np.array([to_coords(f(UB[k]))[0] for k in range(24)]).T
    def acts(Um):
        Um=Um.reshape(5,5); V=np.zeros_like(Um)
        for i in range(5): V[s[i],:]=Um[i,:]
        return V.ravel()
    def actt(Um):
        Um=Um.reshape(5,5); V=np.zeros_like(Um)
        for j in range(5): V[:,t[j]]=Um[:,j]
        return V.ravel()
    S=mat(acts); T=mat(actt)
    za=np.exp(2j*np.pi/a); zb=np.exp(2j*np.pi/b)
    for x in range(a):
        for y in range(b):
            P=sum(za**(-x*k)*zb**(-y*m)*np.linalg.matrix_power(S,k)@np.linalg.matrix_power(T,m) for k in range(a) for m in range(b))/(a*b)
            d=int(round(np.trace(P).real))
            if d: dims[(x,y)]=d
    return a,b,dims
best=[]
names=list(reps)
for i1 in range(len(names)):
    for i2 in range(i1,len(names)):
        s,t=reps[names[i1]],reps[names[i2]]
        a,b,dims=eig_dims(s,t)
        neg=lambda e:((-e[0])%a,(-e[1])%b)
        add=lambda e,f:((e[0]+f[0])%a,(e[1]+f[1])%b)
        cand=[e for e in dims if add(e,e)!=(0,0) and add(add(e,e),e)!=(0,0)]
        # pairs {e,-e}
        pairs=[];seen=set()
        for e in cand:
            if e in seen: continue
            seen.add(e); seen.add(neg(e)); pairs.append((e,neg(e)) if neg(e) in dims else (e,))
        bestv=0;bestE=None
        # each pair: choose none, first, second
        for choice in itertools.product(*[range(len(p)+1) for p in pairs]):
            E=[p[c-1] for p,c in zip(pairs,choice) if c]
            v=sum(dims[e] for e in E)
            if v<=bestv: continue
            Es=set(E); ok=True
            for x in E:
                for y in E:
                    if neg(add(x,y)) in Es: ok=False;break
                if not ok: break
            if ok: bestv=v;bestE=E
        print(names[i1],names[i2],'group',a,b,'max P2P3 weight dim',bestv,bestE,flush=True)
