# verify the closed forms in conic coordinates against direct computation: z = lam w(t), w(t) = chi_1 + 2t chi_2 - 2t^2 chi_3, chi_k(r) = i^{kr}
import numpy as np, itertools
rg=np.random.default_rng(1); I=1j
chi=[np.array([I**(k*r) for r in range(4)]) for k in range(4)]
def w(t): return chi[1]+2*t*chi[2]-2*t*t*chi[3]
def e(ts,k): return sum(np.prod(c) for c in itertools.combinations(ts,k)) if k else 1
t=rg.normal(size=4)+1j*rg.normal(size=4); lam=rg.normal(size=4)+1j*rg.normal(size=4)
Z=[lam[j]*w(t[j]) for j in range(4)]
print('<z0,z1>: direct %.6f%+.6fi  formula %.6f%+.6fi'%(*(lambda v:(v.real,v.imag))(Z[0]@Z[1]),*(lambda v:(v.real,v.imag))(-8*lam[0]*lam[1]*(t[0]-t[1])**2)))
tau=np.sum(Z[0]*Z[1]*Z[2]); g=e(t[:3],1)+4*e(t[:3],2)*e(t[:3],3)
print('tau(z0,z1,z2): direct',np.round(tau,8),' formula',np.round(8*lam[0]*lam[1]*lam[2]*g,8))
q4=np.sum(Z[0]*Z[1]*Z[2]*Z[3]); t2=t**2
f=1+16*e(t,4)+16*e(t,4)**2+4*e(t2,2)-8*sum(t2[l]*e(np.delete(t,l),2) for l in range(4))
print('q4: direct',np.round(q4,8),' formula',np.round(4*np.prod(lam)*f,8))
P4=list(itertools.permutations(range(4))); W=np.array(Z).T
perm=sum(np.prod([W[r,p[r]] for r in range(4)]) for p in P4)
pair=(Z[0]@Z[1])*(Z[2]@Z[3])+(Z[0]@Z[2])*(Z[1]@Z[3])+(Z[0]@Z[3])*(Z[1]@Z[2])
print('perm(W): direct',np.round(perm,8),' pairings - 6 q4',np.round(pair-6*q4,8))
