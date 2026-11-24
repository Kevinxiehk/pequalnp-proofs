# Exact (rational) check of the annihilator dimensions used in section 21 (round 5):
#   K(S) := {Q in A_2 : Q.s = 0 in A_4 for all s in S},  S = V3.V3  or  S = P.V3,  V3 = {alpha,beta}^perp with disjointly supported alpha, beta.
import itertools, random
from fractions import Fraction as Fr
PAIRS=list(itertools.combinations(range(5),2)); IDX={p:i for i,p in enumerate(PAIRS)}
def rank(rows):
    rows=[r[:] for r in rows if any(r)]; rk=0
    if not rows: return 0
    for c in range(len(rows[0])):
        piv=next((i for i in range(rk,len(rows)) if rows[i][c]!=0),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i][c]!=0:
                f=rows[i][c]/rows[rk][c]; rows[i]=[x-f*y for x,y in zip(rows[i],rows[rk])]
        rk+=1
    return rk
def nullspace(rows,n):
    # basis of {x in Q^n : rows x = 0}
    M=[r[:] for r in rows]; piv=[]; rk=0
    for c in range(n):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]; M[rk]=[x/M[rk][c] for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0: M[i]=[x-M[i][c]*y for x,y in zip(M[i],M[rk])]
        piv.append(c); rk+=1
    free=[c for c in range(n) if c not in piv]; out=[]
    for f in free:
        x=[Fr(0)]*n; x[f]=Fr(1)
        for i,c in enumerate(piv): x[c]=-M[i][f]
        out.append(x)
    return out
def prod2(y,z):      # product of two linear forms in A_2
    return [y[j]*z[l]+y[l]*z[j] for (j,l) in PAIRS]
def Kdim(S):         # S: list of elements of A_2; conditions on Q (10 unknowns): (Q.s)[4-set minus m] = sum over disjoint pairs
    rows=[]
    for s in S:
        for m in range(5):
            r=[Fr(0)]*10
            four=[c for c in range(5) if c!=m]
            for p in itertools.combinations(four,2):
                q=tuple(c for c in four if c not in p); r[IDX[p]]+=s[IDX[q]]
            rows.append(r)
    return 10-rank(rows), nullspace(rows,10)
rnd=random.Random(3); g=lambda: Fr(rnd.choice([-5,-4,-3,-2,2,3,4,5,7]))
def V3(A,B):
    al=[Fr(0)]*5; be=[Fr(0)]*5
    for j in A: al[j]=g()
    for j in B: be[j]=g()
    return nullspace([al,be],5),al,be
def span_prod(P,V): return [prod2(y,z) for y in P for z in V]
def comb(V,c): return [sum(ci*v[j] for ci,v in zip(c,V)) for j in range(5)]
print('K(V3.V3) by split type (expected 3,2,1,0,1,0):')
for A,B in (([0],[1]),([0],[1,2]),([0],[1,2,3]),([0],[1,2,3,4]),([0,1],[2,3]),([0,1],[2,3,4])):
    V,al,be=V3(A,B); print('  type',(len(A),len(B)),'dim V3',len(V),' dim K =',Kdim(span_prod(V,V))[0])
print('K(P.V3) for random 2-planes P in V3 (10 random P each): set of dims')
for A,B in (([0],[1,2]),([0],[1,2,3]),([0],[1,2,3,4]),([0,1],[2,3]),([0,1],[2,3,4])):
    V,al,be=V3(A,B); ds=set()
    for _ in range(10):
        P=[comb(V,[g(),g(),g()]),comb(V,[g(),g(),g()])]; ds.add(Kdim(span_prod(P,V))[0])
    print('  type',(len(A),len(B)),' generic P:',sorted(ds))
# special planes
def unit(j): 
    e=[Fr(0)]*5; e[j]=Fr(1); return e
print('special P:')
# type (2,3): A={0,1}, B={2,3,4}: h in C^A, V_B = beta^perp in C^B
V,al,be=V3([0,1],[2,3,4]); h=[al[1],-al[0],Fr(0),Fr(0),Fr(0)]
VB=nullspace([be,unit(0),unit(1)],5)
u0=comb(VB,[g(),g()]); print('  (2,3) P = V_B:',Kdim(span_prod(VB,V))[0],'  P = Ch + Cu0 (u0 generic):',Kdim(span_prod([h,u0],V))[0],end='')
u0s=[Fr(0),Fr(0),be[3],-be[2],Fr(0)]; print('  P = Ch + Cu0 (u0 with a zero):',Kdim(span_prod([h,u0s],V))[0])
# type (2,2,1): A={0,1}, B={2,3}, free column 4
V,al,be=V3([0,1],[2,3]); h=[al[1],-al[0],Fr(0),Fr(0),Fr(0)]; h2=[Fr(0),Fr(0),be[3],-be[2],Fr(0)]; e5=unit(4)
print('  (2,2,1) P = Ce5 + C(xh+x\'h\'):',Kdim(span_prod([e5,comb([h,h2],[g(),g()])],V))[0],'  P = Ce5 + Ch:',Kdim(span_prod([e5,h],V))[0],'  P = C(h+mu e5) + C(h\'+mu\' e5):',Kdim(span_prod([comb([h,e5],[Fr(1),g()]),comb([h2,e5],[Fr(1),g()])],V))[0],'  P = Ch + Ch\':',Kdim(span_prod([h,h2],V))[0])
# type (1,3): A={0}, B={1,2,3}, free column 4
V,al,be=V3([0],[1,2,3]); VB=nullspace([be,unit(0),unit(4)],5); ex=unit(4)
u0=comb(VB,[g(),g()]); u0s=[Fr(0),be[2],-be[1],Fr(0),Fr(0)]
print('  (1,3) P = V_B:',Kdim(span_prod(VB,V))[0],'  P = Ce_x + Cu0 (generic u0):',Kdim(span_prod([ex,u0],V))[0],'  P = Ce_x + Cu0 (u0 with a zero):',Kdim(span_prod([ex,u0s],V))[0])
# type (1,2): A={0}, B={1,2}, C={3,4}
V,al,be=V3([0],[1,2]); hB=[Fr(0),be[2],-be[1],Fr(0),Fr(0)]; c=[Fr(0),Fr(0),Fr(0),g(),g()]; c2=[Fr(0),Fr(0),Fr(0),g(),g()]
print('  (1,2) P = C^C:',Kdim(span_prod([unit(3),unit(4)],V))[0],'  P = Ch_B + Cc:',Kdim(span_prod([hB,c],V))[0],'  P = Cc + C(h_B + c\'):',Kdim(span_prod([c,[a+b for a,b in zip(hB,c2)]],V))[0])
print('type (1,3): K(P.V3) versus "e_x in P" for 30 random P:')
V,al,be=V3([0],[1,2,3]); ex=unit(4); tab={}
for _ in range(30):
    P=[comb(V,[g(),g(),g()]),comb(V,[g(),g(),g()])]
    inP=(rank([P[0],P[1],ex])==2); VBt=nullspace([be,unit(0),unit(4)],5); isVB=(rank([P[0],P[1]]+VBt)==2)
    k=(Kdim(span_prod(P,V))[0],'e_x in P' if inP else ('P = V_B' if isVB else 'other')); tab[k]=tab.get(k,0)+1
print('  ',tab)
