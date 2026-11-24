# G4-A case (a) (R21.9): u, w octahedral vertices on one coordinate plane, w = sg*sqrt3*(other vertex of that plane) (|u| scale 1),
# s_1..s_4 = the four roots of B^v(z) = K(c(z),c(z),v), v = 2u - w.  be, al are then determined (gauge al -> al + mu be is a shift of ka),
# so each configuration is a single plane: test strong levelness directly (perm(J + tY_ka \ col j) - 24 at random t, ka).
import itertools, numpy as np, random
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
def c(s): return np.array([s*s-1, 1j*(s*s+1), 2*s])
def K(a,b,d): return sum(a[p[0]]*b[p[1]]*d[p[2]] for p in itertools.permutations(range(3)))
def perm(M): return sum(np.prod([M[i][s[i]] for i in range(4)]) for s in itertools.permutations(range(4)))
def Bpoly(v):   # coefficients of K(c(z),c(z),v) in z (degree 4), via sampling
    zs=np.arange(5,dtype=complex); vals=[K(c(z),c(z),v) for z in zs]
    return np.linalg.solve(np.vander(zs,5,increasing=True),vals)
random.seed(1); res=[]
for r in range(3):                       # coordinate plane x_r = 0
    o=[i for i in range(3) if i!=r]
    for e in (1j,-1j):
        u=np.zeros(3,dtype=complex); u[o[0]]=1; u[o[1]]=e
        ub=np.zeros(3,dtype=complex); ub[o[0]]=1; ub[o[1]]=-e
        for sg in (1,-1):
            w=sg*np.sqrt(3)*ub; v=2*u-w
            l=np.array([3*K(np.eye(3)[i],u,u)-3*K(np.eye(3)[i],u,w)+K(np.eye(3)[i],w,w) for i in range(3)])
            cf=Bpoly(v); roots=np.roots(cf[::-1]) if abs(cf[4])>1e-9 else None
            if roots is None or len(roots)<4: res.append((r,e,sg,'B^v degree < 4')); continue
            if min(abs(a-b) for a,b in itertools.combinations(roots,2))<1e-7: res.append((r,e,sg,'repeated roots')); continue
            C=[c(s) for s in roots]
            M=np.array(C[1:]).T
            be=[1]+list(np.linalg.solve(M,-C[0])); al=[0]+list(np.linalg.solve(M,3*u-w))
            worst=0
            for ka in (0.3,-1.1+0.4j):
                cols=[(u-(al[k]+ka*be[k])*C[k])/2 for k in range(4)]+[(u-w)/2]
                Y=[H@y for y in cols]
                for t in (0.7,-0.4+1.3j):
                    for j in range(5):
                        cc=[Y[k] for k in range(5) if k!=j]
                        worst=max(worst,abs(perm([[1+t*cc[k][i] for k in range(4)] for i in range(4)])-24))
            res.append((r,e,sg,'|l| = %.1e, max|perm-24| = %.3g'%(np.abs(l).max(),worst)))
for x in res: print('plane x%d=0, u=%s, sign %+d: %s'%(x[0]+1,'(..,1,%s)'%x[1],x[2],x[3]))
