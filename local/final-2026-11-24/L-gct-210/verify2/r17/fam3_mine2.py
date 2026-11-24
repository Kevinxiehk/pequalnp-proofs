# verify2 r17: check stage3's hand computation for the stratum-(III) ANSATZ family (sec. 37 (E)):
# X = {(-b-c+d, b+d rho, c-d(1+rho)) (x) e_0 + b e_1 (x) (0,y) + c e_2 (x) (0,z)}, y, z in C^4.
# Claims: level <=> s(y) = s(z) = <y,z> = 0 (sigma_3 automatic); column sums c(x) = -(0, b y + c z) [given level];
# D_2, D_3 formulas; defect (span of c, D_2, D_3 coefficient vectors) <= 2 <=> y o z in span(y,z).
import sympy as sp, itertools
b,c,d,rho=sp.symbols('b c d rho'); y=sp.symbols('y1:5'); z=sp.symbols('z1:5')
X=sp.zeros(3,5)
X[0,0]=-b-c+d; X[1,0]=b+d*rho; X[2,0]=c-d*(1+rho)
for j in range(4): X[1,j+1]=b*y[j]; X[2,j+1]=c*z[j]
def sig(M,m,cols):
    return sp.expand(sum(sp.prod([M[R[k],C[k]] for k in range(m)]) for R in itertools.combinations(range(M.shape[0]),m) for C in itertools.permutations(cols,m)))
s=[sig(X,m,range(5)) for m in (1,2,3)]
sy,sz,yz=sum(y),sum(z),sum(a*b_ for a,b_ in zip(y,z))
for m,e in zip((1,2,3),s):
    P=sp.Poly(e,b,c,d); print('sigma_%d coefficients (in b,c,d):'%m,[sp.factor(q) for q in P.coeffs()][:8])
# impose level: substitute y4 = -y1-y2-y3, z4 = -z1-z2-z3, and <y,z> = 0 via z3 elimination is messy -> test modulo ideal
sub={y[3]:-y[0]-y[1]-y[2], z[3]:-z[0]-z[1]-z[2]}
z3s=sp.solve(sp.expand(yz.subs(sub)),z[2])[0]; sub2={k:sp.simplify(v.subs(z[2],z3s)) for k,v in sub.items()}; sub2[z[2]]=z3s
class GG:
    def reduce(self,e): return (None, sp.simplify(sp.together(sp.expand(e).subs(sub2,simultaneous=True))))
G=GG()
print('level on the variety s(y)=s(z)=<y,z>=0 (s(y), s(z), <y,z>): all sigma coefficients reduce to 0:',all(G.reduce(sp.expand(q))[1]==0 for e in s for q in sp.Poly(e,b,c,d).coeffs()))
# deletion vectors D_m(x)_j = sigma_m(x minus column j)
D={m:[sig(X,m,[q for q in range(5) if q!=j]) for j in range(5)] for m in (1,2,3)}
cs=[sp.expand(sum(X[i,j] for i in range(3))) for j in range(5)]
print('column sums c(x) =',[sp.factor(G.reduce(q)[1]) for q in cs])
p0=-b-c+d; p1=b+d*rho; p2=c-d*(1+rho)
yo=[0]+[y[j]*z[j] for j in range(4)]; yv=[0]+list(y); zv=[0]+list(z)
D2claim=[p1*b*yv[j]+p2*c*zv[j]+2*b*c*yo[j] for j in range(5)]
D3claim=[2*p0*b*c*yo[j] for j in range(5)]
print('D_2 claim holds modulo level ideal:',all(G.reduce(sp.expand(D[2][j]-D2claim[j]))[1]==0 for j in range(5)))
print('D_3 claim holds modulo level ideal:',all(G.reduce(sp.expand(D[3][j]-D3claim[j]))[1]==0 for j in range(5)))
print('D_1 vs -c(x) (deleting column j: sigma_1 = total - column j):',[sp.factor(G.reduce(sp.expand(D[1][j]+cs[j]))[1]) for j in range(5)])
