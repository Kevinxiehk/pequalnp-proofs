"""Exhaustive Z3 x Z5 graded 3-row spaces: span{1(x)chi_a (a in So), u(x)chi_b (b in Sp), ubar(x)chi_c (c in Sq)}; which are level."""
import sys; sys.path.insert(0,'.')
import numpy as np, itertools
from fast import Pall
from core import u, ub, chi
one=np.array([1,1,1,0,0.])
gens={('o',a):np.outer(one,chi(a)) for a in range(1,5)}
gens.update({('p',b):np.outer(u,chi(b)) for b in range(5)}); gens.update({('q',c):np.outer(ub,chi(c)) for c in range(5)})
keys=list(gens)
rng=np.random.default_rng(0)
def level(B):
    d=len(B); L=np.array([gens[k] for k in B]); A=rng.normal(size=(3*d+6,d))+1j*rng.normal(size=(3*d+6,d))
    X=np.einsum('pi,iab->pab',A,L); return np.abs(Pall(X)[:,1:]).max()<1e-8*max(1,np.abs(X).max()**3)
best={}
# grow: enumerate subsets by increasing size using downward closure (level is closed under subsets)
cur=[()]
for size in range(1,15):
    nxt=set()
    for S in cur:
        for k in keys:
            if S and keys.index(k)<=keys.index(S[-1]): continue
            T=S+(k,)
            if all(tuple(x for x in T if x!=y) in curset for y in T) if size>1 else True:
                if level(list(T)): nxt.add(T)
    if not nxt: break
    cur=sorted(nxt,key=lambda t:[keys.index(x) for x in t]); curset=set(cur)
    if size==1: curset=set(cur)
    print('size',size,'count',len(cur),flush=True)
    last=cur
print('max graded 3-row level dim',len(last[0]),'examples:',last[:6])
import pickle; pickle.dump(last,open('graded4.pkl','wb'))
