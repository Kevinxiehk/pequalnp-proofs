import numpy as np, sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/lemmaz")
from core import *
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def dc45(x):
    c=x.reshape(3,4); g=np.zeros((5,5),complex); g[:3,:4]=c; g[:3,4]=-c.sum(1); g[3,:]=-g[:3].sum(0); return g
ts=[0.0,1.0,-1.0,2.0,-0.5]
def lines(g):
    rn=np.abs(g[:4]).max(1); cn=np.abs(g).max(0); return int((rn<1e-6*np.abs(g).max()).sum()),int((cn<1e-6*np.abs(g).max()).sum())
cnt={}
for st in range(N):
    l1=rng.normal(size=12)+1j*rng.normal(size=12); l2=rng.normal(size=12)+1j*rng.normal(size=12)
    def F(x):
        a=dc45(x[:12]); b=dc45(x[12:])
        out=[minors(a+t*b)[4] for t in ts]
        out.append(np.array([np.sum(a*a),np.sum(a*b),np.sum(b*b),np.sum(a**3),np.sum(a*a*b),np.sum(a*b*b),np.sum(b**3),
                             l1@x[:12]-1,l1@x[12:],l2@x[:12],l2@x[12:]-1]))
        return np.concatenate(out)
    x,r=solve(F,rng.normal(size=24)+1j*rng.normal(size=24),nfev=1200)
    a=dc45(x[:12]); b=dc45(x[12:])
    if r>1e-10: key="no convergence (res>1e-10)"
    else:
        gen=a+0.37*b   # generic element of the plane
        # common zero lines of the plane
        zr=[i for i in range(4) if max(np.abs(a[i]).max(),np.abs(b[i]).max())<1e-6]
        zc=[j for j in range(5) if max(np.abs(a[:,j]).max(),np.abs(b[:,j]).max())<1e-6]
        key="plane found: extra common zero rows %d, common zero cols %d, rank generic %d"%(len(zr),len(zc),int((np.linalg.svd(gen,compute_uv=False)>1e-7).sum()))
    cnt[key]=cnt.get(key,0)+1; print(st,"%.1e"%r,key,flush=True)
for k in sorted(cnt): print(cnt[k],k)
