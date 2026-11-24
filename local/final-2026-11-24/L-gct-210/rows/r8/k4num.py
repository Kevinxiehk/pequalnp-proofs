# K version on exactly NC active columns (Walsh coords): A_0..A_{NC-1} 3x3, sum = 1; residuals: B_j orthogonal (degree 2),
# triple products t(A_a s, A_b s, A_c s) at random s (degree 3), optionally the 4x4 permanent (degree 4, NC = 4), and
# Rabinowitsch z_j * l_j(A_j) = 1 to keep all columns active.  usage: python3 k4num.py SEED NSTARTS NC QUARTIC(0/1)
import numpy as np, sys, itertools
seed,nst,NC,QU=map(int,sys.argv[1:5]); rng=np.random.default_rng(seed)
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex); I3=np.eye(3)
S=rng.normal(size=(24,3))+1j*rng.normal(size=(24,3))
Ls=rng.normal(size=(NC,9))+1j*rng.normal(size=(NC,9))
P3=list(itertools.permutations(range(3))); P4=list(itertools.permutations(range(4)))
def t3(x,y,z): return sum(x[p[0]]*y[p[1]]*z[p[2]] for p in P3)
def unpack(v):
    A=[v[9*j:9*j+9].reshape(3,3) for j in range(NC-1)]; A.append(I3-sum(A)); z=v[9*(NC-1):]; return A,z
def res(v):
    A,z=unpack(v); r=[]
    for M in A:
        B=I3-2*M; r.extend((B.T@B-I3)[np.triu_indices(3)])
    for (a,b,c) in itertools.combinations(range(NC),3):
        for s in S[:14]: r.append(t3(A[a]@s,A[b]@s,A[c]@s))
    if QU and NC==4:
        for s in S[:20]:
            q=H@np.array([A[j]@s for j in range(4)]).T; r.append(sum(np.prod([q[i,p[i]] for i in range(4)]) for p in P4))
    for j in range(NC): r.append(z[j]*(Ls[j]@A[j].ravel())-1)
    return np.array(r)
nv=9*(NC-1)+NC
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
    print('start %d res %.2e column ranks %s |z| %s'%(st,nf,rk,np.round(abs(z),2)),flush=True)
