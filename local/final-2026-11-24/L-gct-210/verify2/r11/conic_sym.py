# verify2 r11: SYMBOLIC check of stage3 33(A) conic-coordinate identities (sympy, exact; I = sqrt(-1))
import sympy as sp, itertools
I=sp.I; t=sp.symbols('t0:4'); l=sp.symbols('l0:4')
chi=[[I**(k*r) for r in range(4)] for k in range(4)]
def w(s): return [chi[1][r]+2*s*chi[2][r]-2*s**2*chi[3][r] for r in range(4)]
Z=[[l[j]*c for c in w(t[j])] for j in range(4)]
dot=lambda a,b: sp.expand(sum(x*y for x,y in zip(a,b)))
e=lambda ts,k: sum(sp.prod(c) for c in itertools.combinations(ts,k)) if k else 1
print('pairing:',sp.simplify(dot(Z[0],Z[1])+8*l[0]*l[1]*(t[0]-t[1])**2)==0)
tau=sp.expand(sum(Z[0][r]*Z[1][r]*Z[2][r] for r in range(4)))
print('tau:',sp.expand(tau-8*l[0]*l[1]*l[2]*(e(t[:3],1)+4*e(t[:3],2)*e(t[:3],3)))==0)
q4=sp.expand(sum(Z[0][r]*Z[1][r]*Z[2][r]*Z[3][r] for r in range(4))); t2=[x**2 for x in t]
f=1+16*e(t,4)+16*e(t,4)**2+4*e(t2,2)-8*sum(t2[k]*e([t[m] for m in range(4) if m!=k],2) for k in range(4))
print('q4:',sp.expand(q4-4*sp.prod(l)*f)==0)
P4=list(itertools.permutations(range(4)))
perm=sp.expand(sum(sp.prod([Z[p[r]][r] for r in range(4)]) for p in P4))
pair=dot(Z[0],Z[1])*dot(Z[2],Z[3])+dot(Z[0],Z[2])*dot(Z[1],Z[3])+dot(Z[0],Z[3])*dot(Z[1],Z[2])
print('perm = pairings - 6 q4:',sp.expand(perm-pair+6*q4)==0)
# general identity check (not only isotropic columns): perm of a 4x4 with sum-zero columns = pairings - 6 q4 ?
a=sp.symbols('a0:16'); M=[[a[4*j+r] for r in range(3)]+[-(a[4*j]+a[4*j+1]+a[4*j+2])] for j in range(4)]
permM=sp.expand(sum(sp.prod([M[p[r]][r] for r in range(4)]) for p in P4))
pr=dot(M[0],M[1])*dot(M[2],M[3])+dot(M[0],M[2])*dot(M[1],M[3])+dot(M[0],M[3])*dot(M[1],M[2])
q=sp.expand(sum(M[0][r]*M[1][r]*M[2][r]*M[3][r] for r in range(4)))
print('general sum-zero columns: perm = pairings - 6 q4:',sp.expand(permM-pr+6*q)==0)
# t = infinity orbit: the line C chi_3 under row permutations
import numpy as np
