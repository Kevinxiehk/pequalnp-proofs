import numpy as np, itertools, re, sys
f=sys.argv[1]; nact=int(sys.argv[2]); P=2147483629
L=open(f).read().split('\n'); names=L[0].split(','); pols=' '.join(L[2:]).split(',')
pols=[q.strip() for q in pols if q.strip()]
rng=np.random.default_rng(3); val={n:rng.normal()+1j*rng.normal() for n in names}
def ev(s):
    tot=0
    for term in s.split('+'):
        fs=term.split('*'); c=int(fs[0]); c=c-P if c>P//2 else c; v=c
        for x in fs[1:]:
            if '^' in x: b,e=x.split('^'); v*=val[b]**int(e)
            else: v*=val[x]
        tot+=v
    return tot
E=np.array([ev(q) for q in pols])
# independent construction
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
X=np.zeros((nact,3),complex); Yp=np.zeros((nact,3),complex)
for a in range(nact):
    for q in range(3):
        X[a,q]=val.get('x%d%d'%(a,q),np.nan); Yp[a,q]=val.get('y%d%d'%(a,q),np.nan)
X[nact-1,0]=1-X[:nact-1,0].sum(); Yp[nact-1,0]=-Yp[:nact-1,0].sum(); Yp[nact-1,1]=1-Yp[:nact-1,1].sum()
assert not np.isnan(X).any() and not np.isnan(Yp).any()
h=np.zeros((4,5),complex); hp=np.zeros((4,5),complex); h[:,:nact]=H@X.T; hp[:,:nact]=H@Yp.T
P4=list(itertools.permutations(range(4)))
def perm(M): return sum(np.prod([M[i,p[i]] for i in range(4)]) for p in P4)
def C(Y):
    J=np.ones((4,5)); return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
# coefficients of s^a t^b (a+b=k, k=1..4) via 2D interpolation on a grid
pts=[(s,t) for s in (0.3,0.7,-0.5,1.1,-0.9) for t in (0.4,-0.6,0.8,1.3,-1.2)]
mons=[(a,b) for k in range(0,5) for a in range(k+1) for b in [k-a]]
A=np.array([[s**a*t**b for (a,b) in mons] for (s,t) in pts])
Cv=np.array([C(s*h+t*hp) for (s,t) in pts]); co=np.linalg.lstsq(A,Cv,rcond=None)[0]
vals=[co[i,j] for i,(a,b) in enumerate(mons) if a+b>=2 for j in range(5)]
vals=np.array(vals)
nz=[e for e in E[:-nact]]
miss=[e for e in nz if np.min(np.abs(vals-e))>1e-6*max(1,abs(e))]
print('equations',len(nz),' matched',len(nz)-len(miss),' unmatched',len(miss))
deg1=[co[i,j] for i,(a,b) in enumerate(mons) if a+b==1 for j in range(5)]
print('degree-1 coefficients (must be 0):',np.max(np.abs(deg1)))
nonzero_direct=[v for v in vals if abs(v)>1e-8]
unmatched_direct=[v for v in nonzero_direct if np.min(np.abs(E[:-nact]-v))>1e-6*max(1,abs(v))]
print('direct nonzero coefficients',len(nonzero_direct),' not among generator equations',len(unmatched_direct))
z=[ev(q) for q in pols[-nact:]]; print('Rabinowitsch rows evaluated (z*x-1):',np.round(z[:2],3))
