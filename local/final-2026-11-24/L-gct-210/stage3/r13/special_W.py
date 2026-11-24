# (alpha0), |supp W| = 4: every column of W lies on one of the 6 special isotropic lines (row permutations of chi_1). Enumerate 4-tuples of
# special lines (with repetition), the kernel of sum l_j v_j = 0, and test: all l_j != 0, all four triple moments tau = 0, perm(W) = 0.
import itertools, numpy as np
lines=[]
for p in itertools.permutations(range(4)):
    v=np.array([1,1j,-1,-1j])[list(p)]
    if not any(abs(abs(np.vdot(v,w))-4)<1e-9 for w in lines): lines.append(v)
print('special lines:',len(lines))
P4=list(itertools.permutations(range(4)))
def perm(W): return sum(np.prod([W[r,q[r]] for r in range(4)]) for q in P4)
found=0; checked=0
for combo in itertools.product(range(len(lines)),repeat=4):
    V=np.array([lines[c] for c in combo]).T                         # 4 x 4, columns v_j
    u,s,vh=np.linalg.svd(V); ns=vh[(s>1e-9).sum():].conj()
    for l in ns:                                                     # kernel vectors (dim 1 or more: test basis + random combos)
        cands=[l]+([ns.T@(np.random.default_rng(1).normal(size=len(ns))+1j*np.random.default_rng(2).normal(size=len(ns)))] if len(ns)>1 else [])
        for lam in cands:
            checked+=1
            if np.min(np.abs(lam))<1e-9*np.max(np.abs(lam)): continue
            W=V*lam[None,:]; W=W/np.abs(W).max()
            taus=[abs(np.sum(W[:,a]*W[:,b]*W[:,c])) for a,b,c in itertools.combinations(range(4),3)]
            pm=abs(perm(W))
            if max(taus)<1e-9 and pm<1e-9: found+=1; print('W candidate: lines',combo,'lambda',np.round(lam,4))
print('checked',checked,'kernel vectors; W candidates with all columns special, all lambda != 0, tau = 0, perm = 0:',found)
