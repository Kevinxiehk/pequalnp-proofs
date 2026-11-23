import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
import numpy as np, itertools
from test_algebra import mul, lin, SUB, IDX, rank
rng=np.random.default_rng(12)
def prod(rows):
    w=lin(rows[0]); k=1
    for r in rows[1:]: w=mul(w,k,lin(r),1); k+=1
    return w
# type (2,2,1): V_i = lam_i h + mu_i h' + nu_i e_5, h on cols 0,1 ; h' on cols 2,3
al=rng.normal(size=2); be=rng.normal(size=2)
h=np.array([al[1],-al[0],0,0,0]); hp=np.array([0,0,be[1],-be[0],0]); e5=np.eye(5)[4]
H2=prod([h,h]); Hp2=prod([hp,hp])
m220=mul(H2,2,Hp2,2); m211=mul(mul(H2,2,lin(hp),1),3,lin(e5),1); m121=mul(mul(lin(h),1,Hp2,2),3,lin(e5),1)
lam,mu,nu=rng.normal(size=4),rng.normal(size=4),rng.normal(size=4)
P=prod([lam[i]*h+mu[i]*hp+nu[i]*e5 for i in range(4)])
F220=sum(lam[a]*lam[b]*np.prod([mu[c] for c in range(4) if c not in (a,b)]) for a,b in itertools.combinations(range(4),2))
F211=sum(lam[a]*lam[b]*mu[c]*nu[d] for a,b in itertools.combinations(range(4),2) for c in range(4) if c not in (a,b) for d in range(4) if d not in (a,b,c))
F121=sum(mu[a]*mu[b]*lam[c]*nu[d] for a,b in itertools.combinations(range(4),2) for c in range(4) if c not in (a,b) for d in range(4) if d not in (a,b,c))
print('(2,2,1): product = F220 H^2H\'^2 + F211 H^2H\'y + F121 HH\'^2y : err %.1e ; the three monomials independent: rank %d'%(np.abs(P-(F220*m220+F211*m211+F121*m121)).max(),rank(np.array([m220,m211,m121]))))
# type (2,3,0): V_i = lam_i h + om_i, om_i in beta^perp of C^{2,3,4}
bet=rng.normal(size=3); B=np.linalg.svd(bet[None])[2][1:]   # basis of V_beta in C^3
om=[np.concatenate([[0,0],rng.normal(size=2)@B]) for _ in range(4)]
P=prod([lam[i]*h+om[i] for i in range(4)])
t1=sum(lam[k]*mul(lin(h),1,prod([om[i] for i in range(4) if i!=k]),3) for k in range(4))
t2=sum(lam[a]*lam[b]*mul(H2,2,prod([om[i] for i in range(4) if i not in (a,b)]),2) for a,b in itertools.combinations(range(4),2))
print('(2,3,0): product = H*sum_k lam_k Om^3 + H^2*sum lam_S Om^2 : err %.1e'%np.abs(P-t1-t2).max())
# binary cubic w3 w4 w5 on V_beta has three distinct roots (discriminant != 0): check polar form has no singular direction
c=lambda w: w[0]*w[1]*w[2]
roots=[np.cross(bet,np.eye(3)[i]) for i in range(3)]
print('    three root lines of the cubic on V_beta pairwise independent:',all(rank(np.array([roots[i],roots[j]]))==2 for i,j in itertools.combinations(range(3),2)))
# concurrent case v_0 = e_j: the two forbidden support triples really have nonzero triple product
def tp(vs): return np.abs(prod(vs)).max()
e=np.eye(5)
print('path 12,23,34: %.2f ; star 12,13,14: %.2f ; matching+loop 12,34,e1: %.2f'%(tp([e[1]+2*e[2],e[2]-e[3],3*e[3]+e[4]]),tp([e[1]+e[2],e[1]-2*e[3],e[1]+e[4]]),tp([e[1]+e[2],e[3]+e[4],e[1]])))
