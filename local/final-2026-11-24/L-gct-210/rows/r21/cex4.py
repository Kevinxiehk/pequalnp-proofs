# Candidate counterexample to (SM4) / (SM4''): rank-2 columns in the Walsh coordinate plane x3 = 0.
# Direct check: Y (4x5) with columns H y_k (k=1..4) and a zero 5th column; perm(J + t Y \ col j) == 24 for all t, j.
import itertools, cmath
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
def perm(M):
    n=len(M); return sum(__import__('math').prod(M[i][s[i]] for i in range(n)) for s in itertools.permutations(range(n)))
def check(ys,label):
    cols=[[sum(H[r][c]*y[c] for c in range(3)) for r in range(4)] for y in ys]+[[0]*4]
    f=[sum(y[c] for y in ys) for c in range(3)]
    worst=0
    for t in (0.37,1.0,-2.3+0.7j,3.1j,5.0):
        for j in range(5):
            cc=[cols[k] for k in range(5) if k!=j]
            M=[[1+t*cc[k][r] for k in range(4)] for r in range(4)]
            worst=max(worst,abs(perm(M)-24))
    print(label,'f =',[complex(round(x.real,12),round(x.imag,12)) for x in map(complex,f)],'f.f =',round(abs(sum(x*x for x in f)),12),
          'min|col| =',round(min(max(abs(v) for v in c) for c in cols[:4]),6),' max|perm-24| over t,j =',worst)
s3=3**0.5; i=1j
# (a) isotropic f = (1,i,0), t = sqrt3, w = 1 (exact family from R21.3)
check([((s3+1)/2,-i*(s3-1)/2,0),((1-s3)/2,i*(s3+1)/2,0),(0.5,i/2,0),(-0.5,-i/2,0)],'(a) iso, P4 imposed:')
# (b) non-isotropic f = (2,0,0), Thales circle, real (degree 2,3 only; P4 not imposed)
a=(1-0.3**2)**0.5; b=(1-0.7**2)**0.5
check([(0.7,a,0),(0.7,-a,0),(0.3,b,0),(0.3,-b,0)],'(b) non-iso, no P4:')
