# Round 13: (alpha0) reduces to SHAPE S: Y = a (x) (1,1,1,1,-2)^T + b (x) (e_3 - e_4)^T, a in V nonzero, b in V isotropic.  The line C Y must have
# defect in C m0: t^k-coefficients of C_1 - C_0, C_2 - C_0, C_3 - C_0, C_4 + 4 C_0 - 120 vanish (C_j(tY) = perm(J_4 + t Y^(j))).
# Exact system over Q: a = (a0,a1,a2,-a0-a1-a2), b likewise with sum b_r^2 = 0; chart a_i = 1 (i = 0,1,2; a != 0 and homogeneity).
import sys, itertools, sympy as sp
t=sp.Symbol('t'); A=sp.symbols('a0:3'); B=sp.symbols('b0:3')
def build(i):
    a=list(A)+[-sum(A)]; a[i]=sp.Integer(1); a[3]=-(a[0]+a[1]+a[2]); b=list(B)+[-sum(B)]
    Y=sp.Matrix(4,5,lambda r,c: a[r]*[1,1,1,1,-2][c]+b[r]*[0,0,0,1,-1][c])
    C=[]
    for j in range(5):
        M=sp.Matrix(4,4,lambda r,c: 1+t*Y[r,[x for x in range(5) if x!=j][c]]); C.append(sp.expand(M.per()))
    eqs=[]
    for D in (C[1]-C[0],C[2]-C[0],C[3]-C[0],C[4]+4*C[0]-120):
        eqs+=[e for e in sp.Poly(sp.expand(D),t).all_coeffs() if e!=0]
    eqs.append(sp.expand(sum(x**2 for x in b)))
    vs=[x for k,x in enumerate(A) if k!=i]+list(B)
    return eqs,vs
for i in range(3):
    eqs,vs=build(i)
    with open('/home/kevxhk/work/L-gct-210/stage3/r13/shapeS_%d.sing'%i,'w') as fh:
        fh.write('ring R=0,(%s),dp;\nideal I=%s;\nideal G=std(I);\n"SHAPE_S chart %d: size",size(G),"dim",dim(G);\nG;\nquit;\n'%(','.join(map(str,vs)),',\n'.join(str(e).replace('**','^') for e in eqs),i))
    print('chart',i,'equations',len(eqs),flush=True)
