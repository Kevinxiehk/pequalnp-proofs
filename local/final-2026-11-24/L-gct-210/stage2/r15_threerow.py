# Target 2, three-row case, numerical census with m FREE [NOTES-stage2 R15-3]. Unknowns: P = span(p1,p2) (3x5 each, rows a,b,c) and m in C^5 (sum 0,
# normalised). Conditions (reduced level conditions of R14-2, polarised over P) + C4:
#   (L) c(p) in C m;  (Q0) P_2(p) = 0;  (Q) (P_2(p minus col j))_j in span(1,m);  (C4) all 3x3 subpermanents of p vanish;  for all p in P.
# Forced: all three rows nonzero (row norms 1) and >= 3 columns nonzero (columns 0,1,2 norm >= 0.3 via slack). Every hit is classified.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
SEED=int(sys.argv[1]) if len(sys.argv)>1 else 1; NTR=int(sys.argv[2]) if len(sys.argv)>2 else 12; MODE=sys.argv[3] if len(sys.argv)>3 else '3col'
rg=np.random.default_rng(SEED)
P3=list(itertools.permutations(range(3))); TR=list(itertools.combinations(range(5),3))
def perm3(M): return sum(M[0,p[0]]*M[1,p[1]]*M[2,p[2]] for p in P3)
def P2(M):
    n,k=M.shape; tot=0
    for i in range(n):
        for i2 in range(i+1,n):
            tot+=M[i].sum()*M[i2].sum()-M[i]@M[i2]
    return tot
AB=[(1,0),(0,1),(1,1),(1,-1),(1,2),(2,1),(1,1j)]
def unpack(x):
    z=x[:len(x)//2]+1j*x[len(x)//2:]
    p=z[:30].reshape(2,3,5); m=z[30:35]; return p,m
def res(x):
    p,m=unpack(x); out=[]
    one=np.ones(5)
    for (al,be) in AB:
        M=al*p[0]+be*p[1]
        c=M.sum(axis=0)
        # (L): c in Cm  <=>  c wedge m = 0  (all 2x2 minors)
        for i in range(5):
            for j in range(i+1,5): out.append(c[i]*m[j]-c[j]*m[i])
        out.append(P2(M))                                            # (Q0)
        v=np.array([P2(np.delete(M,j,axis=1)) for j in range(5)])
        # (Q): v in span(1,m): the 3x3 minors of [1; m; v] vanish
        A=np.vstack([one,m,v])
        for cols in TR: out.append(np.linalg.det(A[:,cols]))
        for S in TR: out.append(perm3(M[:,S]))                       # (C4)
    out.append(m.sum()); out.append(np.vdot(m,m)-1)                   # m normalisation
    g=p.reshape(2,15)@p.reshape(2,15).conj().T; out+=[g[0,1],g[1,0]]
    for i in range(3): out.append(np.sum(np.abs(p[:,i,:])**2)-1.0)
    if MODE=='3col':
        for j in range(3): out.append(np.sum(np.abs(p[:,:,j])**2)-0.3)
    o=np.array(out,dtype=complex); return np.concatenate([o.real,o.imag])
hits=0
for tr in range(NTR):
    x0=rg.normal(size=70)
    s=least_squares(res,x0,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=6000)
    nr=np.linalg.norm(s.fun)
    if nr<1e-8:
        p,m=unpack(s.x); cols=[j for j in range(5) if np.abs(p[:,:,j]).max()>1e-6]; hits+=1
        print('trial %2d res %.1e: columns %s, m = %s, <m,m> = %.2e'%(tr,nr,cols,np.round(m,3),abs(m@m)),flush=True)
    else: print('trial %2d res %.2e'%(tr,nr),flush=True)
print('hits',hits,'of',NTR)
