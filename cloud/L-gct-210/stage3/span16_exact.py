import itertools
from fractions import Fraction
# exact rank (over Q) of the span of the six subspaces W_ik = p_ik (x) p_ki (x) P (x) P in (C^2)^{(x)4}
def tensor(fac):
    t=[Fraction(1)]
    for f in fac: t=[a*b for a in t for b in f]
    return t
def rank(rows):
    rows=[r[:] for r in rows]; rk=0; n=len(rows[0])
    for c in range(n):
        piv=next((i for i in range(rk,len(rows)) if rows[i][c]!=0),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i][c]!=0:
                f=rows[i][c]/rows[rk][c]; rows[i]=[a-f*b for a,b in zip(rows[i],rows[rk])]
        rk+=1
    return rk
E=[[Fraction(1),Fraction(0)],[Fraction(0),Fraction(1)]]
def span_dim(marks):
    vecs=[]
    for i,k in itertools.combinations(range(4),2):
        rest=[x for x in range(4) if x not in (i,k)]
        for f1 in E:
            for f2 in E:
                fac=[None]*4; fac[i]=marks[i][k]; fac[k]=marks[k][i]; fac[rest[0]]=f1; fac[rest[1]]=f2
                vecs.append(tensor(fac))
    return rank(vecs)
e1=[Fraction(1),Fraction(0)]; e2=[Fraction(0),Fraction(1)]; e12=[Fraction(1),Fraction(1)]
def normal(i,classes):  # classes: list of lists of partners; pairwise non-proportional class vectors e1, e2, e1+e2
    d={}
    for v,cl in zip([e1,e2,e12],classes):
        for k in cl: d[k]=v
    return d
others=lambda i:[k for k in range(4) if k!=i]
no_coinc=[normal(i,[[k] for k in others(i)]) for i in range(4)]
print('no coincidence (normal form e1,e2,e1+e2 in each plane): exact rank',span_dim(no_coinc))
tri=[normal(0,[[1,2],[3]]),normal(1,[[0,2],[3]]),normal(2,[[0,1],[3]]),normal(3,[[0],[1],[2]])]
print('exactly one triangle {0,1,2}: exact rank',span_dim(tri))
coll=[normal(i,[others(i)]) for i in range(4)]
print('collapsed 4-set (all proportional in every plane): exact rank',span_dim(coll))
