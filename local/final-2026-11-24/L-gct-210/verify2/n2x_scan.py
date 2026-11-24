# verify2: N2-X (beta-1): scan of ALL small-integer positions of P inside V_3 (after the torus normalisation alpha = 1_A, beta = 1_B, which is
# legitimate because column scalings are automorphisms of A).  For every P compute dim K(P V_3) exactly and compare with the value claimed
# for its sub-case; report deviations, and whether a 1-dim K is spanned by a monomial (which would defeat the (R1) argument).
import itertools, random
from fractions import Fraction as Fr
src=open('/home/kevxhk/work/L-gct-210/verify2/n2x_annihilators2.py').read().split("ok=True; terms=set()")[0]
exec(src)
def rk(vs): return ex7.rank([list(v) for v in vs]) if vs else 0
def planes_in(V3,rng_=range(-2,3)):
    """all 2-planes spanned by small integer combinations of the basis V3 (canonical by reduced coefficient matrix)"""
    seen={}; cs=[c for c in itertools.product(rng_,repeat=3) if any(c)]
    for c1,c2 in itertools.combinations(cs,2):
        M=[[Fr(x) for x in c1],[Fr(x) for x in c2]]
        # rref
        r=0
        for col in range(3):
            p=next((i for i in range(r,2) if M[i][col]!=0),None)
            if p is None: continue
            M[r],M[p]=M[p],M[r]; pv=M[r][col]; M[r]=[x/pv for x in M[r]]
            for i in range(2):
                if i!=r and M[i][col]!=0:
                    f=M[i][col]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
            r+=1
            if r==2: break
        if r<2: continue
        key=tuple(tuple(x) for x in M)
        if key not in seen: seen[key]=[[sum(M[i][k]*V3[k][j] for k in range(3)) for j in range(5)] for i in range(2)]
    return seen
def contains(P,v): return rk(P+[v])==2
def mono(K): return len(K)==1 and sum(1 for x in K[0] if x!=0)==1
report={}
def note(typ,case,d,claim,K):
    key=(typ,case,d,claim,'MONOMIAL' if mono(K) else ''); report[key]=report.get(key,0)+1
# (2,3): A={0,1}, B={2,3,4}; V3 = C h + V_B
h=vec({0:1,1:-1}); u0=vec({2:1,3:-1}); u1=vec({3:1,4:-1})
for key,P in planes_in([h,u0,u1]).items():
    K=nullvec(cond_rows(PV(P,[h,u0,u1])))
    if not contains(P,h) and rk(P+[u0,u1])==2: case,claim='P = V_B',1
    elif contains(P,h): case,claim='P = Cu0 + Ch',1
    else: case,claim='P = Cu0 + C(h+u1)',0
    note('(2,3)',case,len(K),claim,K)
# (2,2): A={0,1}, B={2,3}, free 4
hp=vec({2:1,3:-1}); e4=vec({4:1})
for key,P in planes_in([h,hp,e4]).items():
    K=nullvec(cond_rows(PV(P,[h,hp,e4])))
    if not contains(P,e4): case,claim='e5 not in P',1
    elif contains(P,h) or contains(P,hp): case,claim='P = Ce5 + Ch (or h\')',2
    else: case,claim='P = Ce5 + C(xh+x\'h\')',1
    note('(2,2)',case,len(K),claim,K)
# (1,3): alpha = e_0, B={1,2,3}, x = 4
v0=vec({1:1,2:-1}); v1=vec({2:1,3:-1})
for key,P in planes_in([v0,v1,e4]).items():
    K=nullvec(cond_rows(PV(P,[v0,v1,e4])))
    if not contains(P,e4): case,claim='P = V_B or e_x not in P',1
    else: case,claim='P = Ce_x + Cu0',2
    note('(1,3)',case,len(K),claim,K)
# (1,4): alpha = e_0, beta = 1 on {1,2,3,4}
w0=vec({1:1,2:-1}); w1=vec({2:1,3:-1}); w2=vec({3:1,4:-1})
for key,P in planes_in([w0,w1,w2]).items():
    K=nullvec(cond_rows(PV(P,[w0,w1,w2]))); note('(1,4)','any P',len(K),1,K)
# (1,2): alpha = e_0, B={1,2}, C={3,4}
hB=vec({1:1,2:-1}); e3=vec({3:1})
for key,P in planes_in([hB,e3,e4]).items():
    K=nullvec(cond_rows(PV(P,[hB,e3,e4])))
    if contains(P,e3) and contains(P,e4): case,claim='P = C^C',3
    else: case,claim='P != C^C',2
    note('(1,2)',case,len(K),claim,K)
print('type, sub-case, dim K found, dim K claimed, flag  ->  number of planes P')
for k,v in sorted(report.items(),key=str): print('  ',k,v,'' if k[2]==k[3] else '   <-- DEVIATION')
