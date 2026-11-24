import numpy as np, itertools, sys, collections
def basis(t):
    return np.array([1,0,t[0],t[1],t[2]],complex), np.array([0,1,t[3],t[4],t[5]],complex)
def e2(v): return sum(v[i]*v[j] for i,j in itertools.combinations(range(5),2))
def d3a(a):
    A=a.sum(); return np.array([-a[j]*(e2(a)-A*a[j]+a[j]**2) for j in range(5)])
def d2(a,b): A=a.sum(); B=b.sum(); return A*b+B*a-2*a*b
def nodes(W):
    Q,_=np.linalg.qr(W.T); P=Q@Q.conj().T
    return tuple(k for k in range(5) if np.linalg.norm(np.eye(5)[k]-P@np.eye(5)[k])<1e-4)
rng=np.random.default_rng(0)
sols=np.concatenate([np.load(f) for f in sys.argv[1:]]) if len(sys.argv)>1 else np.load('pairs_sols_1.npy')
# dedupe across files
U=[]
for t in sols:
    if not any(np.linalg.norm(t-s)<1e-6 for s in U): U.append(t)
stats=collections.Counter(); neutral_ok=collections.Counter()
for t in U:
    a1,a2=basis(t[:6]); b1,b2=basis(t[6:]); Wa=np.array([a1,a2]); Wb=np.array([b1,b2])
    V=[]
    for _ in range(10):
        x=rng.normal(size=2)+1j*rng.normal(size=2); y=rng.normal(size=2)+1j*rng.normal(size=2)
        a=x@Wa; b=y@Wb; V+= [d2(a,b), d3a(a), d3a(b)]
    V=np.array(V); s=np.linalg.svd(V,compute_uv=False); e=int((s>1e-5*s[0]).sum())
    same=np.linalg.svd(np.vstack([Wa,Wb]),compute_uv=False)[2]<1e-4
    na,nb=nodes(Wa),nodes(Wb)
    key=(e, 'same' if same else 'diff', len(na), len(nb))
    stats[key]+=1
    if e==3:
        # neutral column?  defect inside e_k^perp for some k
        Q=np.linalg.svd(V)[2][:3]
        neut=[k for k in range(5) if np.abs(Q[:,k]).max()<1e-4]
        neutral_ok[(tuple(neut),na,nb)]+=1
print('distinct solutions',len(U))
for k,v in sorted(stats.items()): print('  e=%d %s nodes(a)=%d nodes(b)=%d : %d'%(k[0],k[1],k[2],k[3],v))
print('e=3 details (neutral columns, nodes a, nodes b):',dict(neutral_ok))
