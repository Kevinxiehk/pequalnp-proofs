# verify2: MIN-A rank claim. Tensor space (C^2)^{(x)4} for rows a,b,c,d (index 0..3). In plane P_i the marked line toward k is p[i][k].
# Subspaces: for each pair {i,k}: p_ik (x) p_ki (x) P_l (x) P_m. Claim: span = 16 if 0 or 1 triangle; 11 if collapsed.
import itertools, random
from fractions import Fraction as Fr
def rank(rows):
    M=[[Fr(x) for x in r] for r in rows]; r=0
    for c in range(len(M[0])):
        p=None
        for i in range(r,len(M)):
            if M[i][c]!=0: p=i; break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
        if r==len(M): break
    return r
def tensor(vs):
    out=[1]
    for v in vs: out=[x*y for x in out for y in v]
    return out
def span_rank(p):
    rows=[]
    E=[[1,0],[0,1]]
    for i,k in itertools.combinations(range(4),2):
        l,m=[x for x in range(4) if x not in (i,k)]
        for el in E:
            for em in E:
                vs=[None]*4; vs[i]=p[i][k]; vs[k]=p[k][i]; vs[l]=el; vs[m]=em
                rows.append(tensor(vs))
    return rank(rows)
e1=[1,0]; e2=[0,1]; e12=[1,1]
# 0 triangles: three distinct lines in each plane
def others(i): return [k for k in range(4) if k!=i]
p0={i:{k:v for k,v in zip(others(i),(e1,e2,e12))} for i in range(4)}
print('0 triangles, standard labelling: rank',span_rank(p0))
# all labellings (should be the same by GL_2^4, check anyway) and random distinct lines
rs=set()
for perms in itertools.product(itertools.permutations((e1,e2,e12)),repeat=4):
    p={i:{k:v for k,v in zip(others(i),perms[i])} for i in range(4)}
    rs.add(span_rank(p))
print('0 triangles, all 6^4 labellings: ranks',rs)
random.seed(1); rs=set()
for _ in range(200):
    p={}
    for i in range(4):
        while True:
            vs=[[random.randint(-5,5),random.randint(-5,5)] for _ in range(3)]
            if all(vs[x][0]*vs[y][1]-vs[x][1]*vs[y][0]!=0 for x in range(3) for y in range(x+1,3)): break
        p[i]={k:v for k,v in zip(others(i),vs)}
    rs.add(span_rank(p))
print('0 triangles, 200 random integer line triples: ranks',rs)
# exactly one triangle abc = (0,1,2): p_ab || p_ac, p_ba || p_bc, p_ca || p_cb; d generic
p1={0:{1:e1,2:e1,3:e2},1:{0:e1,2:e1,3:e2},2:{0:e1,1:e1,3:e2},3:{0:e1,1:e2,2:e12}}
print('1 triangle: rank',span_rank(p1))
rs=set()
for _ in range(200):
    p={}
    for i in range(3):
        while True:
            u=[random.randint(-5,5),random.randint(-5,5)]; v=[random.randint(-5,5),random.randint(-5,5)]
            if u[0]*v[1]-u[1]*v[0]!=0: break
        o=[k for k in range(3) if k!=i]
        cc=random.choice([1,2,-3]); p[i]={o[0]:u,o[1]:[cc*x for x in u],3:v}
    while True:
        vs=[[random.randint(-5,5),random.randint(-5,5)] for _ in range(3)]
        if all(vs[x][0]*vs[y][1]-vs[x][1]*vs[y][0]!=0 for x in range(3) for y in range(x+1,3)): break
    p[3]={k:v for k,v in zip((0,1,2),vs)}
    rs.add(span_rank(p))
print('1 triangle, 200 random: ranks',rs)
# collapsed: all lines in each plane equal
pc={i:{k:e1 for k in others(i)} for i in range(4)}
print('collapsed: rank',span_rank(pc))
