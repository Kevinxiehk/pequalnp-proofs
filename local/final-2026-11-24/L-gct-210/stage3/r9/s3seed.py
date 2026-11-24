# Round 9, S3-1 (seeded): one/two-vector extension of known 7-dim level spaces with single-row parts (lifts of rows' 4x5 spaces
# (4,1) -> z = 3, (5,2) -> z = 2, (6,3) -> z = 1), holomorphic LM of rows/clm.py (P_1..P_5 at N sample points, Grassmann chart).
# MODES: cal7  = random 6-dim subspace of a seed + one random vector -> dim 7   (CALIBRATION: must converge in a positive fraction)
#        ext8  = seed + one random vector -> dim 8 (TARGET);   ext9 = seed + two random vectors -> dim 9 (TARGET)
# perturbation: the seed basis is perturbed by EPS (relative) before the start, so the LM may move the seed along its moduli.
# usage: python3 -I s3seed.py MODE SEED0 NSTARTS EPS
import sys, glob, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff')
import numpy as np, build7, clm, oracle
from math import comb
mode,s0,ns,EPS=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]); FO=int(sys.argv[5]) if len(sys.argv)>5 else 0
import itertools
P4=np.array(list(itertools.permutations(range(4))))
def cofs(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4].prod(axis=1).sum())
    return np.array(out)
def T1(B,rg,n=None):
    d=len(B); n=n or 3*25
    A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=d)+1j*rg.normal(size=d))*0.7,B,axes=1)) for _ in range(n)])
    u,s,vh=np.linalg.svd(A); r=int((s>1e-7*s[0]).sum()); N=vh[r:].conj()          # t with A t = 0 (bilinear)
    Q=np.linalg.qr(B.reshape(d,-1).T)[0]; N=N-(N@Q.conj())@Q.T                      # remove the part in span(B) (Hermitian projection)
    u2,s2,vh2=np.linalg.svd(N); k=int((s2>1e-6*max(1,s2[0])).sum()); return vh2[:k], 25-r

files=sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d[456]_defect[123]_s*.npy'))
seeds=[]
for f in files:
    B,e=build7.build(np.load(f))
    if len(B)==7 and build7.check(B)<1e-6: seeds.append((f.split('/')[-1],B))
print('seeds (7-dim, level):',len(seeds),flush=True)
def chart(Bm,P):
    X=Bm.reshape(len(Bm),-1)@P.Pi.conj().T; d=len(Bm); return np.linalg.solve(X[:,:d],X[:,d:]).ravel()
def invariants(B,tol=1e-6):
    d=len(B); R=range(5)
    def rk(A): s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
    def ker(rows): return d-rk(np.array([[B[k][i,j] for k in range(d)] for i in rows for j in R]))
    return dict(a=[5-rk(B[:,r,:]) for r in R], b=[5-rk(B[:,:,c]) for c in R], z=[ker([i for i in R if i!=r]) for r in R],
                zc=[d-rk(np.array([[B[k][i,j] for k in range(d)] for j in R if j!=c for i in R])) for c in R])
t0=time.time(); hits=0; res=[]
for st in range(s0,s0+ns):
    rg=np.random.default_rng(10000+st); name,B=seeds[st%len(seeds)]
    B=B/np.linalg.norm(B.reshape(7,-1),axis=1)[:,None,None]
    B=B+EPS*(rg.normal(size=B.shape)+1j*rg.normal(size=B.shape))
    def rv(base=None):
        if FO and base is not None:
            E,dT=T1(base,rg)
            if len(E): t=(rg.normal(size=len(E))+1j*rg.normal(size=len(E)))@E; return (t/np.linalg.norm(t)).reshape(5,5)
        t=rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)); return t/np.linalg.norm(t)
    if mode.startswith('near'):   # planted: random 6-dim subspace S of the seed + (a seed vector outside S) + DELTA * noise, DELTA = float(mode[4:])
        dl=float(mode[4:]); C=rg.normal(size=(6,7))+1j*rg.normal(size=(6,7)); S=np.einsum('ik,kab->iab',C,B)
        Q=np.linalg.qr(S.reshape(6,-1).T)[0]; t=B.reshape(7,-1)[st%7]; t=t-(Q@(Q.conj().T@t)); t=t/np.linalg.norm(t)
        t=t+dl*rv().ravel(); Bs=np.concatenate([S,[t.reshape(5,5)]]); d=7
    elif mode=='cal7': C=rg.normal(size=(6,7))+1j*rg.normal(size=(6,7)); S=np.einsum('ik,kab->iab',C,B); Bs=np.concatenate([S,[rv(S)]]); d=7
    elif mode=='ext8': Bs=np.concatenate([B,[rv(B)]]); d=8
    else: Bs=np.concatenate([B,[rv(B)],[rv()]]); d=9
    N=2*comb(d+4,5)
    P=clm.Problem(5,d,'level',seed=st,N=N)
    import os; z,c=clm.solve(P,z0=chart(Bs,P),iters=int(os.environ.get("ITERS","250")))
    res.append(c); info=''
    if c<1e-7:
        Z=P.basis(z); lev=oracle.level_error_5x5(Z,n=60,seed=st+5); rk=np.linalg.matrix_rank(Z.reshape(d,-1),1e-7)
        info=' HIT fresh-level-err %.1e rank %d %s'%(lev,rk,invariants(Z))
        if lev<1e-6 and rk==d: hits+=1; np.save('/home/kevxhk/work/L-gct-210/stage3/r9/hits_%s_%d.npy'%(mode,st),Z)
    print('start %d seed %s res %.2e%s  (t=%.0f s)'%(st,name,c,info,time.time()-t0),flush=True)
print('MODE %s EPS %g: starts %d, verified hits %d, residual quantiles %s'%(mode,EPS,ns,hits,np.round(np.quantile(res,[0,.25,.5]),8)),flush=True)
