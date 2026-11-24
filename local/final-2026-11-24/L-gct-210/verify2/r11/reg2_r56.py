# verify2 r11: exact sample check of reg2 rounds 5-6 families (own generator, Fractions): level, dim T', exact rank q (2 base points), FO2 bound.
import sys
exec(open('/home/kevxhk/work/L-gct-210/verify2/r8/reg2_fo2_special.py').read().split("B=[outer_row(0,[4,-1,-1,-1,-1])")[0])
def lev(B):
    d=len(B)
    return all(perm([[F(1)]*5]*0+[[F(1)+sum(cc[q]*B[q][i][l] for q in range(d)) for l in range(5)] for i in range(4)]+[[F(1)]*5])==120 for cc in [[F(random.randint(-6,6)) for _ in range(d)] for _ in range(10)])
def run(name,B):
    print('%-30s dim %d level %s'%(name,len(B),lev(B)),flush=True); fo2(name,B)
# BB: U0 = span(e0-e1, e0-e2) row 0; U1 = span(5e3-1, 5e4-1) row 1; columns 3, 4: x, x' in {x_1 = 0, sum 0}, x perp x'
x=[1,0,2,-3]; xp=[5,0,-4,-1]
run('BB p=2',[outer_row(0,[1,-1,0,0,0]),outer_row(0,[1,0,-1,0,0]),outer_row(1,[-1,-1,-1,4,-1]),outer_row(1,[-1,-1,-1,-1,4]),outer_col(x,3),outer_col(xp,4)])
# BD: U1 = span(5e3-1, v), v = (1,v1,v2,0,-1-v1-v2); U0 = (U1 + C1)^perp; x = (2,0,-1,-1) col 3, x' = (0,0,1,-1) col 4
v=[1,2,3,0,-6]; U1=[[-1,-1,-1,4,-1],v]; U0=null([[1]*5]+U1,5)
run('BD v=(1,2,3,0,-6)',[outer_row(0,w) for w in U0]+[outer_row(1,u) for u in U1]+[outer_col([2,0,-1,-1],3),outer_col([0,0,1,-1],4)])
# BLOCK (t,a): row 0: {1,m}^perp, row 2: m, block {x e_1^T + a (Jx) e_4^T : x in V}, V = {x_0 = 0, sum 0}, Jx = (0, x2-x3, x3-x1, x1-x2)
def block(t,a):
    m=[F(t),0,-1-F(t),1,0]; R0=null([[1]*5,m],5)
    Bs=[outer_row(0,w) for w in R0]+[outer_row(2,m)]
    for xv in ([0,1,-1,0],[0,0,1,-1]):
        Jx=[0,xv[2]-xv[3],xv[3]-xv[1],xv[1]-xv[2]]
        M=[[F(0)]*5 for _ in range(4)]
        for i in range(4): M[i][1]=F(xv[i]); M[i][4]=F(a)*Jx[i]
        Bs.append(M)
    return Bs
run('BLOCK (t,a)=(2,3)',block(2,3)); run('BLOCK (t,a)=(1,1) [reg2: (10,4,8)]',block(1,1))
# DOUBLE-BLOCK (a,b): row 0: {(al,be,g,g,g): al+be+3g = 0}; {x e_0^T + a (Jx) e_1^T : x in V}; {e_2 w^T + b e_3 (J'w)^T : w in W'}
def dblock(a,b):
    Bs=[outer_row(0,[1,-1,0,0,0]),outer_row(0,[3,0,-1,-1,-1])]
    for xv in ([0,1,-1,0],[0,0,1,-1]):
        Jx=[0,xv[2]-xv[3],xv[3]-xv[1],xv[1]-xv[2]]
        M=[[F(0)]*5 for _ in range(4)]
        for i in range(4): M[i][0]=F(xv[i]); M[i][1]=F(a)*Jx[i]
        Bs.append(M)
    for w in ([0,0,1,-1,0],[0,0,0,1,-1]):
        Jw=[0,0,w[3]-w[4],w[4]-w[2],w[2]-w[3]]
        M=[[F(0)]*5 for _ in range(4)]
        for l in range(5): M[2][l]=F(w[l]); M[3][l]=F(b)*Jw[l]
        Bs.append(M)
    return Bs
run('DOUBLE-BLOCK (a,b)=(2,3)',dblock(2,3)); run('DOUBLE-BLOCK (1,1) [reg2: (10,4,8)]',dblock(1,1))
