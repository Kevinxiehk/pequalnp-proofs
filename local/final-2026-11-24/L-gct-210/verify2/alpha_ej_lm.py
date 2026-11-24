# verify2: numerical treatment (LM in logarithmic coordinates: support exact) of the support patterns that survive the exact monomial
# filter (alpha_ej_all.py) with max support size 3 or 4.  First entry of every vector gauged to 1.
import itertools, sys, pickle, time, numpy as np
from scipy.optimize import least_squares
surv=pickle.load(open('/home/kevxhk/work/L-gct-210/verify2/alpha_surv.pkl','rb'))
cols=range(4); triples=list(itertools.combinations(range(5),3)); S3=list(itertools.combinations(cols,3)); P3=list(itertools.permutations(range(3)))
def name(m): return ''.join(str(j) for j in cols if m>>j&1)
rng=np.random.default_rng(5); t0=time.time(); out=[]; tcap=float(sys.argv[1]) if len(sys.argv)>1 else 150
for pat in surv:
    if max(bin(m).count('1') for m in pat)<=2: continue
    cells=[(i,j) for i in range(5) for j in cols if pat[i]>>j&1]
    first={i:min(j for j in cols if pat[i]>>j&1) for i in range(5)}
    free=[c for c in cells if c[1]!=first[c[0]]]; idx={c:k for k,c in enumerate(free)}; n=len(free)
    A=[];B=[];C=[];seg=[]; ne=0
    for tr in triples:
        for S in S3:
            ms=[tuple((tr[i],S[p[i]]) for i in range(3)) for p in P3 if all(pat[tr[i]]>>S[p[i]]&1 for i in range(3))]
            if not ms: continue
            for mono in ms:
                ii=[idx.get(c,n) for c in mono]; A.append(ii[0]); B.append(ii[1]); C.append(ii[2]); seg.append(ne)
            ne+=1
    A=np.array(A);B=np.array(B);C=np.array(C);seg=np.array(seg)
    def res(z):
        zc=np.concatenate([z[:n]+1j*z[n:],[0]])
        e=np.exp(zc[A]+zc[B]+zc[C])
        return np.concatenate([np.bincount(seg,weights=e.real,minlength=ne),np.bincount(seg,weights=e.imag,minlength=ne)])
    best=(1e9,None)
    for s in range(10):
        z0=np.concatenate([rng.normal(size=n)*0.8,rng.uniform(-np.pi,np.pi,size=n)])
        sol=least_squares(res,z0,method='lm' if 2*ne>=2*n else 'trf',max_nfev=600)
        r=np.linalg.norm(sol.fun); zr=np.abs(sol.x[:n]).max() if n else 0
        if zr<12 and r<best[0]: best=(r,zr)
        if time.time()-t0>tcap: break
    out.append((best[0],best[1],[name(m) for m in pat],n,ne))
    if time.time()-t0>tcap: break
out.sort(key=lambda t:t[0])
print('patterns treated:',len(out),' time %.0fs'%(time.time()-t0))
print('patterns with a bounded numerical solution (res < 1e-8):',sum(1 for o in out if o[0]<1e-8))
for o in out[:12]: print('  best bounded residual %.2e (max|log| %s)  pattern %s  unknowns %d equations %d'%(o[0],'%.1f'%o[1] if o[1] is not None else '-',o[2],o[3],o[4]))
