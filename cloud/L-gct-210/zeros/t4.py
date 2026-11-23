import sympy as sp, itertools
I=sp.I
chi=lambda a: [I**(a*j) for j in range(4)]
th=sp.symbols('t1:6')
def v(t): return [sp.expand(chi(1)[k]+t*chi(2)[k]-t**2/2*chi(3)[k]) for k in range(4)]
def perm(cols):
    return sp.expand(sum(sp.prod([cols[j][s[j]] for j in range(4)]) for s in itertools.permutations(range(4))))
V=[v(t) for t in th]
# sanity: isotropic and sum zero
print([sp.expand(sum(x for x in V[0])), sp.expand(sum(x*x for x in V[0]))])
p=sp.factor(perm(V[:4])); print('perm[v1..v4] =',p)
# with v(inf)=chi3 in place of v4
p2=sp.factor(perm(V[:3]+[chi(3)])); print('perm[v1,v2,v3,chi3] =',p2)
# cubic invariants
tau=lambda a,b,c: sp.expand(sum(a[k]*b[k]*c[k] for k in range(4)))
print('tau(v1^3)=',sp.factor(tau(V[0],V[0],V[0])),' tau(v1 v2^2)=',sp.factor(tau(V[0],V[1],V[1])))
print('tau(v1^2 chi3)=',sp.factor(tau(V[0],V[0],chi(3))),' tau(v1 chi3^2)=',sp.factor(tau(V[0],chi(3),chi(3))),' tau(chi3^3)=',tau(chi(3),chi(3),chi(3)))
