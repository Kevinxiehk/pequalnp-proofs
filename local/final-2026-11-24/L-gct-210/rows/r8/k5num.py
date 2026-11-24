# K version on NC active columns, degree 2 + 3 only.  Cubic for NC columns: for each j, F_j = sum_{k<l, k,l != j} t(y_j,y_k,y_l) == 0
# (y = A s), which for NC = 4 is equivalent to "all four triples vanish" and for NC = 3 to "the triple vanishes".
# Rabinowitsch z_j l_j(A_j) = 1 keeps all columns active.   usage: python3 k5num.py SEED NSTARTS NC [SIGNS]
import numpy as np, sys, itertools
seed,nst,NC=map(int,sys.argv[1:4]); SG=sys.argv[4] if len(sys.argv)>4 else None
rng=np.random.default_rng(seed); I3=np.eye(3)
S=rng.normal(size=(14,3))+1j*rng.normal(size=(14,3)); Ls=rng.normal(size=(NC,9))+1j*rng.normal(size=(NC,9))
P3=list(itertools.permutations(range(3)))
def t3(x,y,z): return sum(x[p[0]]*y[p[1]]*z[p[2]] for p in P3)
def unpack(v):
    A=[v[9*j:9*j+9].reshape(3,3) for j in range(NC-1)]; A.append(I3-sum(A)); return A,v[9*(NC-1):]
def res(v):
    A,z=unpack(v); r=[]
    for M in A:
        B=I3-2*M; r.extend((B.T@B-I3)[np.triu_indices(3)])
    if SG:
        for M,sg in zip(A,SG): r.append(np.linalg.det(I3-2*M)-(1 if sg=='+' else -1))
    for s in S:
        y=[M@s for M in A]
        for j in range(NC):
            r.append(sum(t3(y[j],y[k],y[l]) for k,l in itertools.combinations([q for q in range(NC) if q!=j],2)))
    for j in range(NC): r.append(z[j]*(Ls[j]@A[j].ravel())-1)
    return np.array(r)
nv=9*(NC-1)+NC; hits=0
for st in range(nst):
    v=rng.normal(size=nv)+1j*rng.normal(size=nv); lam=1e-3; f=res(v); nf=np.linalg.norm(f)
    for it in range(250):
        if nf<1e-12: break
        J=np.zeros((len(f),nv),complex)
        for k in range(nv):
            e=np.zeros(nv,complex); e[k]=1e-7; J[:,k]=(res(v+e)-f)/1e-7
        dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(nv),-J.conj().T@f,rcond=None)[0]; f2=res(v+dx)
        if np.linalg.norm(f2)<nf: v=v+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    A,z=unpack(v); rk=[int(np.sum(np.linalg.svd(M,compute_uv=False)>1e-6)) for M in A]
    hits+=nf<1e-10
    print('start %d res %.2e ranks %s max|z| %.1f'%(st,nf,rk,max(abs(z))),flush=True)
print('HITS',hits,'of',nst)
