import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/stage3")
import itertools
from fractions import Fraction
from span16_exact import tensor, rank, E, e1, e2, e12
# 4-set {a,b,c,d} = {0,1,2,3} where the pair (0,1) carries a 2-dim space of 2-row elements (m_01 = 2) and the other five pairs
# carry lines. T1 gives mu = 0 on W_ik = p_ik (x) p_ki (x) P (x) P for the five pairs != (0,1). Do they span the 16-dim space?
def span_dim(marks,pairs):
    vecs=[]
    for i,k in pairs:
        rest=[x for x in range(4) if x not in (i,k)]
        for f1 in E:
            for f2 in E:
                fac=[None]*4; fac[i]=marks[i][k]; fac[k]=marks[k][i]; fac[rest[0]]=f1; fac[rest[1]]=f2
                vecs.append(tensor(fac))
    return rank(vecs)
five=[(0,2),(0,3),(1,2),(1,3),(2,3)]
m3=[Fraction(1),Fraction(-2)]
def cfg(tri_acd,tri_bcd):
    M=[{},{},{},{}]
    M[0][2]=e1; M[0][3]=e1 if tri_acd else e2
    M[1][2]=e1; M[1][3]=e1 if tri_bcd else e2
    # P_c (index 2): partners 0,1,3 ; P_d (index 3): partners 0,1,2
    for i,(x,y) in ((2,3),(3,2)), :
        pass
    M[2][0]=e1; M[2][1]=e2; M[2][3]=e12
    M[3][0]=e1; M[3][1]=e2; M[3][2]=e12
    if tri_acd: M[2][3]=M[2][0]; M[3][2]=M[3][0]
    if tri_bcd:
        if tri_acd: M[2][1]=M[2][0]; M[3][1]=M[3][0]
        else: M[2][3]=M[2][1]; M[3][2]=M[3][1]
    return M
for ta,tb in ((0,0),(1,0),(0,1),(1,1)):
    print('triangles acd:%d bcd:%d -> exact rank of the five subspaces: %d of 16'%(ta,tb,span_dim(cfg(ta,tb),five)))
