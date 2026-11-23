# verify2: independent check of MIN-C (alpha), case v_0 = e_j:
#   CLAIM: there are no five nonzero vectors pi_1..pi_5 in C^4 with all ten triple products Pi_b Pi_c Pi_d = 0 in the squarefree algebra
#   (i.e. all 3x3 subpermanents of every 3x4 matrix of three distinct pi's vanish), supports covering all 4 columns (NZ), and no three
#   of them proportional to the same unit vector (NT).
# Method: enumerate support patterns (multisets of 5 nonempty subsets of [4]) up to column permutations; filter NZ, NT; discard patterns
# where some coefficient is a single monomial (cannot vanish with nonzero entries); for the rest run LM in logarithmic coordinates
# (entries = exp(z), so the support is exact) from several starts and report the best residual with bounded |z|.
import itertools, sys, time, numpy as np
from scipy.optimize import least_squares
cols=range(4); perms4=list(itertools.permutations(cols))
def pm(mask,p): return sum(1<<p[j] for j in cols if mask>>j&1)
pats=set()
for t in itertools.combinations_with_replacement(range(1,16),5):
    pats.add(min(tuple(sorted(pm(m,p) for m in t)) for p in perms4))
pats=sorted(pats)
triples=list(itertools.combinations(range(5),3)); S3=list(itertools.combinations(cols,3)); P3=list(itertools.permutations(range(3)))
def monos(pat):
    out=[]
    for tr in triples:
        for S in S3:
            ms=[tuple((tr[i],S[p[i]]) for i in range(3)) for p in P3 if all(pat[tr[i]]>>S[p[i]]&1 for i in range(3))]
            if ms: out.append(ms)
    return out
stat={'total':len(pats),'NZ fails':0,'NT fails':0,'single-monomial coefficient':0,'no equations (trivially solvable!)':0,'LM: no solution':0,'LM: SOLUTION':0}
sols=[]; rng=np.random.default_rng(3); t0=time.time(); worst=None
for pat in pats:
    u=0
    for m in pat: u|=m
    if u!=15: stat['NZ fails']+=1; continue
    if any(pat.count(1<<j)>=3 for j in cols): stat['NT fails']+=1; continue
    eqs=monos(pat)
    if any(len(ms)==1 for ms in eqs): stat['single-monomial coefficient']+=1; continue
    if not eqs: stat['no equations (trivially solvable!)']+=1; sols.append((pat,None)); continue
    cells=[(i,j) for i in range(5) for j in cols if pat[i]>>j&1]; idx={c:k for k,c in enumerate(cells)}; n=len(cells)
    E=[[ [idx[c] for c in mono] for mono in ms] for ms in eqs]
    def res(z):
        zc=z[:n]+1j*z[n:]
        r=np.array([sum(np.exp(zc[m[0]]+zc[m[1]]+zc[m[2]]) for m in ms) for ms in E])
        return np.concatenate([r.real,r.imag])
    best=1e9; bz=None
    for s in range(12):
        z0=np.concatenate([rng.normal(size=n)*0.7,rng.uniform(-np.pi,np.pi,size=n)])
        if 2*len(E)<2*n:   # underdetermined: pad
            sol=least_squares(res,z0,method='trf',max_nfev=300)
        else:
            sol=least_squares(res,z0,method='lm',max_nfev=300)
        r=np.linalg.norm(sol.fun); zmax=np.abs(sol.x[:n]).max()
        # normalise: entries exp(z); solution counts only if entries stay bounded away from 0 and infinity relative to each row
        zc=sol.x[:n]
        spread=max(max(zc[[idx[c] for c in cells if c[0]==i]])-min(zc[[idx[c] for c in cells if c[0]==i]]) for i in range(5))
        scale=np.exp(min(zc))**3
        rel=r/max(scale,1e-300)
        if spread<25 and rel<best: best=rel; bz=(r,spread)
    if best<1e-8: stat['LM: SOLUTION']+=1; sols.append((pat,bz))
    else:
        stat['LM: no solution']+=1
        if worst is None or best<worst[0]: worst=(best,pat)
for k,v in stat.items(): print('%-40s %d'%(k,v))
print('smallest relative residual among "no solution" patterns:',worst)
for s in sols[:20]: print('  SOLUTION pattern (support masks):',s)
print('time %.1fs'%(time.time()-t0))
