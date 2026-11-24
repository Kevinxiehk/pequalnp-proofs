# Round 15: line conditions in CHI-COORDINATES over Q (no i needed). A vector x of V = 1^perp in C^4 is x = x1 chi_1 + x2 chi_2 + x3 chi_3,
# chi_k(r) = i^{kr}. Then  <x,y> = sum_r x_r y_r = 4 (x1 y3 + x3 y1 + x2 y2),  tau(x,y,z) = sum_r x_r y_r z_r = 4 sum_{k+l+m = 0 mod 4} x_k y_l z_m,
# q4(x,y,z,w) = 4 sum_{k+l+m+n = 0 mod 4} x_k y_l z_m w_n.  For column-centred X (4x4, columns x_1..x_4):
# perm(J + tX) = 24 - 2 t^2 sum_{pairs} <,> + 2 t^3 sum_{triples} tau + t^4 (sum_{pairings} <,><,> - 6 q4).
import itertools
def ip(x,y): return '4*((%s)*(%s)+(%s)*(%s)+(%s)*(%s))'%(x[0],y[2],x[2],y[0],x[1],y[1])
T3=[k for k in itertools.product((1,2,3),repeat=3) if sum(k)%4==0]
T4=[k for k in itertools.product((1,2,3),repeat=4) if sum(k)%4==0]
def tau(x,y,z): return '4*('+'+'.join('(%s)*(%s)*(%s)'%(x[k-1],y[l-1],z[m-1]) for k,l,m in T3)+')'
def q4(x,y,z,w): return '4*('+'+'.join('(%s)*(%s)*(%s)*(%s)'%(x[k-1],y[l-1],z[m-1],w[n-1]) for k,l,m,n in T4)+')'
def coeffs(cols):
    """degree-2,3,4 coefficients of perm(J + tX) - 24 for 4 column-centred columns (chi-coordinates, strings)"""
    c2='-2*('+'+'.join(ip(cols[a],cols[b]) for a,b in itertools.combinations(range(4),2))+')'
    c3='2*('+'+'.join(tau(cols[a],cols[b],cols[c]) for a,b,c in itertools.combinations(range(4),3))+')'
    P=[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]
    c4='('+'+'.join('(%s)*(%s)'%(ip(cols[a],cols[b]),ip(cols[c],cols[d])) for (a,b),(c,d) in P)+')-6*'+q4(*cols)
    return [c2,c3,c4]
def line_eqs(Ycols):
    """Ycols: 5 columns (chi-coords). Defect in C m0: C_j = C_0 (j=1,2,3), C_4 + 4 C_0 = 120, degree by degree (2,3,4)."""
    C=[coeffs([Ycols[c] for c in range(5) if c!=j]) for j in range(5)]
    out=[]
    for d in range(3):
        for j in (1,2,3): out.append('(%s)-(%s)'%(C[j][d],C[0][d]))
        out.append('(%s)+4*(%s)'%(C[4][d],C[0][d]))
    return out
if __name__=='__main__':   # numerical self-check against brute-force permanents
    import numpy as np, random
    I=1j; chi=[np.array([I**(k*r) for r in range(4)]) for k in range(4)]
    P4=list(itertools.permutations(range(4)))
    def perm4(M): return sum(np.prod([M[r,p[r]] for r in range(4)]) for p in P4)
    rg=np.random.default_rng(1); X=rg.normal(size=(4,3))+1j*rg.normal(size=(4,3))
    cols=[[repr(complex(v)) for v in X[c]] for c in range(4)]
    full=[sum(X[c][k]*chi[k+1] for k in range(3)) for c in range(4)]
    M=np.array(full).T
    for tt in (0.3,-0.7):
        bf=perm4(np.ones((4,4))+tt*M)-24
        cs=[eval(s.replace('^','**')) for s in coeffs(cols)]
        print('t=%g brute %s formula %s'%(tt,np.round(bf,10),np.round(cs[0]*tt**2+cs[1]*tt**3+cs[2]*tt**4,10)))
