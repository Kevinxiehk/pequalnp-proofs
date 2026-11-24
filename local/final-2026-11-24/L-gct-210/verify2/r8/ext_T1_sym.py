# verify2 r9: T'(X(sg)) over Q(sg) for D04-PROP alpha = (1,1,-1,-1): cofactor annihilator at 40 integer points, exact over QQ(sg).
import random, json, sympy as sp, itertools
from sympy.polys.matrices import DomainMatrix
sg=sp.Symbol('sg'); random.seed(23)
def mk():
    B=[]
    v=[0]*25
    for i,cv in enumerate([sg,-1-sg,0,1]): v[(i+1)*5]=cv
    B.append(v)
    for row,w in ((2,(-4,1,1,1,1)),(2,(0,1,1,-1,-1)),(3,(0,1,-1,0,0)),(3,(0,0,0,1,-1))):
        v=[0]*25
        for l in range(5): v[(row+1)*5+l]=w[l]
        B.append(v)
    return B
X=mk()
def perm(M):
    n=len(M)
    if n==0: return sp.Integer(1)
    return sp.expand(sum(M[0][j]*perm([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n) if M[0][j]!=0))
rows=[]
for _ in range(40):
    c=[random.randint(-5,5) for _ in range(5)]
    M=[[1+sum(c[q]*X[q][i*5+j] for q in range(5)) for j in range(5)] for i in range(5)]
    rows.append([perm([[M[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]) for i in range(5) for j in range(5)])
K=sp.QQ.frac_field(sg)
DM=DomainMatrix([[K.convert(e) for e in r] for r in rows],(40,25),K)
NS=DM.nullspace()
T=[[K.to_sympy(e) for e in row] for row in NS.to_Matrix().tolist()] if hasattr(NS,'to_Matrix') else NS.to_Matrix().tolist()
print('dim T\' over Q(sg) =',len(T),flush=True)
# complement of X in T (over Q(sg)), then clear denominators
basis=[list(map(sp.sympify,x)) for x in X]; U=[]
def rk(vs): return sp.Matrix(vs).rank(simplify=True)
r0=rk(basis)
for t in T:
    if rk(basis+[t])>len(basis): basis.append(t); U.append(t)
Up=[]
for u in U:
    den=sp.lcm([sp.denom(sp.together(e)) for e in u]); w=[sp.factor(sp.together(e*den)) for e in u]
    g=sp.gcd_list([sp.expand(e) for e in w if e!=0]); w=[sp.expand(sp.cancel(e/g)) for e in w]; Up.append(w)
print('complement',len(Up))
dens=set()
for u in U:
    for e in u: dens.add(sp.factor(sp.denom(sp.together(e))))
print('denominators of the raw complement:',dens)
json.dump({'X':[[str(e) for e in x] for x in X],'U':[[str(e) for e in u] for u in Up]},open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1_sym.json','w'))
