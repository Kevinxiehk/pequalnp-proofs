# exact check of a candidate counterexample to CONJECTURE K0 (sub-case (1,1)):
# S = {(x a, y b)}, a = (s,s,1,2,-3), s = -3/7, b = e_0 - e_1.  Isotropic-coordinate formulas (R2.5): P2 = 3(sum a b - A B),
# P3 = 6(e3(a) + e3(b)); deletion defects d2_k, d3_k = P2, P3 of the 4 columns j != k.  Forms in (x,y) as dicts {(i,j): coeff}.
from fractions import Fraction as Fr
from itertools import combinations
def mul(p,q):
    r={}
    for (a,b),c in p.items():
        for (d,e),f in q.items(): r[(a+d,b+e)]=r.get((a+d,b+e),0)+c*f
    return {k:v for k,v in r.items() if v!=0}
def add(*ps):
    r={}
    for p in ps:
        for k,v in p.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v!=0}
def sc(c,p): return {k:c*v for k,v in p.items() if c*v!=0}
def e3(v):
    r={}
    for i,j,k in combinations(range(len(v)),3): r=add(r,mul(mul(v[i],v[j]),v[k]))
    return r
s=Fr(-3,7); av=[s,s,Fr(1),Fr(2),Fr(-3)]; bv=[Fr(1),Fr(-1),0,0,0]
X={(1,0):Fr(1)}; Y={(0,1):Fr(1)}
a=[sc(c,X) for c in av]; b=[sc(c,Y) for c in bv]
def P2(idx): return sc(3,add(*[mul(a[j],b[j]) for j in idx], sc(-1,mul(add(*[a[j] for j in idx]),add(*[b[j] for j in idx])))))
def P3(idx): return sc(6,add(e3([a[j] for j in idx]),e3([b[j] for j in idx])))
al=range(5)
print('P2 =',P2(al),' P3 =',P3(al))
for k in al:
    idx=[j for j in al if j!=k]; print('k=%d  d2 ='%k,P2(idx),'  d3 =',P3(idx))
