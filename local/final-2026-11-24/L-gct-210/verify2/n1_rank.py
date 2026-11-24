# verify2: N1 / Lemma Q4-gen rank claims by an independent method (exact polynomial coefficient vectors, integer arithmetic).
# Normal forms (parameters t0..t4), coordinates of xi_a, xi_b, xi_c, xi_d in bases of the planes P_a..P_d (derived independently, see notes):
#  A (one pair ab with m=2, no triangle acd):   xa=(v1+al, v2+be) xb=(v1,v2) xc=(al,ga) xd=(be,ga)
#  B (one pair ab with m=2, triangle acd):      xa=(v1+al+be, v2+de) xb=(v1,v2) xc=(al,de) xd=(be,de)   [w indep. of p is FORCED]
#  C (two pairs ab, cd with m=2):               xa=(v1+de, v2) xb=(v1,v2) xc=(u1+de,u2) xd=(u1,u2)
import itertools
from fractions import Fraction as Fr
def lin(*idx):
    p={}
    for i in idx:
        e=[0]*5; e[i]=1; p[tuple(e)]=p.get(tuple(e),0)+1
    return p
def mul(p,q):
    r={}
    for a,ca in p.items():
        for b,cb in q.items():
            k=tuple(x+y for x,y in zip(a,b)); r[k]=r.get(k,0)+ca*cb
    return {k:v for k,v in r.items() if v}
def rank(rows):
    M=[[Fr(x) for x in r] for r in rows]; rk=0
    for c in range(len(M[0])):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        rk+=1
        if rk==len(M): break
    return rk
forms={'A':((lin(0,2),lin(1,3)),(lin(0),lin(1)),(lin(2),lin(4)),(lin(3),lin(4))),
       'B':((lin(0,2,3),lin(1,4)),(lin(0),lin(1)),(lin(2),lin(4)),(lin(3),lin(4))),
       'C':((lin(0,4),lin(1)),(lin(0),lin(1)),(lin(2,4),lin(3)),(lin(2),lin(3)))}
for name,(a,b,c,d) in forms.items():
    polys=[mul(mul(a[e[0]],b[e[1]]),mul(c[e[2]],d[e[3]])) for e in itertools.product(range(2),repeat=4)]
    monos=sorted(set(k for p in polys for k in p))
    print('normal form',name,': rank of the 16 quartics =',rank([[p.get(m,0) for m in monos] for p in polys]),' (monomials: %d)'%len(monos))
