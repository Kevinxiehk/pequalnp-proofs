# verify2: independent numerical search for a counterexample to stage2's Lemma N2-GEN.
# Unknowns: weights a_j = exp(al_j), b_j = exp(be_j) (zero-free by construction), a 2-plane P of C^5 in a chart (pivots j1, j2).
# Equations (necessary for "X level"):  (i) sum a lam = sum b lam = sigma;  (ii) sum c lam^2 = sigma^2 for c in {a, b, ab};
# (iii) sum ab lam^3 = sigma^3, as polynomial identities on P (coefficients in the basis p1, p2).  A solution is GENUINE if the weights
# stay bounded (|Re log| < 8) and P contains no unit vector.
import sys, itertools, numpy as np, time
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0); tmax=float(sys.argv[2]) if len(sys.argv)>2 else 100
def unpack(z,piv):
    zc=z[:16]+1j*z[16:]; a=np.exp(zc[:5]); b=np.exp(zc[5:10]); oth=[k for k in range(5) if k not in piv]
    P=np.zeros((2,5),complex); P[0,piv[0]]=1; P[1,piv[1]]=1; P[0,oth]=zc[10:13]; P[1,oth]=zc[13:16]
    return a,b,P
def res(z,piv):
    a,b,P=unpack(z,piv); p,q=P; sp=p.sum(); sq=q.sum(); r=[]
    for c in (a,b): r+=[(c*p).sum()-sp,(c*q).sum()-sq]
    for c in (a,b,a*b): r+=[(c*p*p).sum()-sp*sp,(c*p*q).sum()-sp*sq,(c*q*q).sum()-sq*sq]
    c=a*b; r+=[(c*p**3).sum()-sp**3,(c*p*p*q).sum()-sp*sp*sq,(c*p*q*q).sum()-sp*sq*sq,(c*q**3).sum()-sq**3]
    r=np.array(r); return np.concatenate([r.real,r.imag])
t0=time.time(); n=0; zeros=0; genuine=0; cls={'weight -> 0 or infinity':0,'unit vector in P':0,'chart blow-up':0}; ex=None
while time.time()-t0<tmax:
    piv=sorted(rng.choice(5,size=2,replace=False)); z0=np.concatenate([rng.normal(size=16)*0.7,rng.uniform(-np.pi,np.pi,size=10),rng.normal(size=6)*0.7])
    sol=least_squares(res,z0,args=(piv,),method='lm',max_nfev=800); n+=1
    if np.linalg.norm(sol.fun)>1e-9: continue
    zeros+=1; a,b,P=unpack(sol.x,piv)
    wmax=np.abs(sol.x[:10]).max()
    # unit vector in P: smallest singular value of [P; e_j] drops
    dist=min(np.linalg.svd(np.vstack([P,np.eye(5)[j]]),compute_uv=False)[-1] for j in range(5))
    if wmax>8: cls['weight -> 0 or infinity']+=1
    elif np.abs(P).max()>1e3: cls['chart blow-up']+=1
    elif dist<1e-4: cls['unit vector in P']+=1
    else: genuine+=1; ex=(a,b,P)
print('starts',n,' zeros (residual < 1e-9):',zeros,' classification:',cls,' GENUINE:',genuine)
if ex is not None:
    np.set_printoptions(precision=4,suppress=True,linewidth=200); print('a =',ex[0]); print('b =',ex[1]); print('P =',ex[2])
