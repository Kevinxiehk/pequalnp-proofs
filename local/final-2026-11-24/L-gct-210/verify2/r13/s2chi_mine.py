# verify2 r13: LEMMA S2 via the column-centred permanent formula (verified symbolically by me in r11):
#   perm(J4 + tX) = 24 - 2t^2 sum_{p<q} <x_p,x_q> + 2t^3 sum_{p<q<r} tau(x_p,x_q,x_r) + t^4 (sum_3 pairings <,><,> - 6 q4(x_0..x_3))  (columns sum-zero)
# in chi-coordinates (x = x1 chi_1 + x2 chi_2 + x3 chi_3; structure constants computed HERE from chi_k(r) = i^{kr}, all rational).
# Y columns: a, a, a + b2, a + b3, -2a - b2 - b3; b2 = (1, 2 t2, -2 t2^2), b3 = be (1, 2 t3, -2 t3^2) (or t3 = t2 for 'par').
# usage: MODE (neq|par|cal) ACHART (1|2|3) P (0 or prime)    [self-test against direct permanents on random rational data first]
import sys, itertools, sympy as sp
mode,ach,P=sys.argv[1],int(sys.argv[2]),sys.argv[3]
I=sp.I; chi=[[I**(k*r) for r in range(4)] for k in (1,2,3)]
G2=[[sp.nsimplify(sum(chi[i][r]*chi[j][r] for r in range(4))) for j in range(3)] for i in range(3)]
G3={(i,j,k):sp.nsimplify(sum(chi[i][r]*chi[j][r]*chi[k][r] for r in range(4))) for i in range(3) for j in range(3) for k in range(3)}
G4={(i,j,k,l):sp.nsimplify(sum(chi[i][r]*chi[j][r]*chi[k][r]*chi[l][r] for r in range(4))) for i in range(3) for j in range(3) for k in range(3) for l in range(3)}
assert all(x.is_rational for row in G2 for x in row) and all(x.is_rational for x in G3.values()) and all(x.is_rational for x in G4.values())
ip=lambda x,y: sum(G2[i][j]*x[i]*y[j] for i in range(3) for j in range(3))
tau=lambda x,y,z: sum(G3[(i,j,k)]*x[i]*y[j]*z[k] for i in range(3) for j in range(3) for k in range(3))
q4=lambda x,y,z,w: sum(G4[(i,j,k,l)]*x[i]*y[j]*z[k]*w[l] for i in range(3) for j in range(3) for k in range(3) for l in range(3))
t=sp.Symbol('t')
def permform(X):
    p2=sum(ip(X[p],X[q]) for p,q in itertools.combinations(range(4),2))
    p3=sum(tau(X[p],X[q],X[r]) for p,q,r in itertools.combinations(range(4),3))
    pr=ip(X[0],X[1])*ip(X[2],X[3])+ip(X[0],X[2])*ip(X[1],X[3])+ip(X[0],X[3])*ip(X[1],X[2])
    return 24-2*t**2*p2+2*t**3*p3+t**4*(pr-6*q4(*X))
# self-test: random rational chi-coordinates -> standard coordinates -> direct permanent
import random
random.seed(7)
cols=[[sp.Rational(random.randint(-5,5),random.randint(1,3)) for _ in range(3)] for _ in range(4)]
std=[[sum(c[i]*chi[i][r] for i in range(3)) for r in range(4)] for c in cols]
direct=sp.expand(sum(sp.prod([1+t*std[p[r]][r] for r in range(4)]) for p in itertools.permutations(range(4))))
assert sp.expand(direct-permform(cols))==0, 'formula self-test failed'
a1,a2,a3,t2,t3,be,u,v=sp.symbols('a1 a2 a3 t2 t3 be u v')
a=[a1,a2,a3]; b2=[1,2*t2,-2*t2**2]; tt3=t2 if mode=='par' else t3; b3=[be,2*be*tt3,-2*be*tt3**2]
add=lambda *vs: [sum(v_[k] for v_ in vs) for k in range(3)]; sc=lambda c,x: [c*y for y in x]
Y=[a,a,add(a,b2),add(a,b3),add(sc(-2,a),sc(-1,b2),sc(-1,b3))]
C=[sp.expand(permform([Y[c] for c in range(5) if c!=j])) for j in range(5)]
D=[C[1]-C[0],C[2]-C[0],C[3]-C[0],C[4]+4*C[0]-120]
eqs=[]
for d_ in D: eqs+=[e for e in sp.Poly(sp.expand(d_),t).all_coeffs() if e!=0]
rab={'neq':u*be*(t2-t3)-1,'par':u*be*(be-1)-1,'cal':u*be-1}[mode]
eqs+=[rab, v*a[ach-1]-1]
vs='a1,a2,a3,t2,'+('' if mode=='par' else 't3,')+'be,u,v'
s='ring R=%s,(%s),dp; option(redSB);\nideal I=%s;\nideal G=std(I);\nprintf("S2CHI %s achart %d char %s: dim %%s unit %%s",dim(G),reduce(1,G)==0);\nquit;\n'%(
   P,vs,',\n'.join(str(sp.expand(e)).replace('**','^') for e in eqs),mode,ach,P)
open('s2c_%s_%d_%s.sing'%(mode,ach,'q' if P=='0' else 'p'),'w').write(s); print('written; self-test passed;',len(eqs),'equations')
