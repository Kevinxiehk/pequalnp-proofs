# Round 14: line conditions of SHAPE S2: Y = a (x) (1,1,1,1,-2)^T + b2 (x) (e_2 - e_4)^T + b3 (x) (e_3 - e_4)^T, a in V (chart a_i = 1), b2, b3 in V
# isotropic. Dimension of the solution variety (exact over Q), and with p_3(b2) != 0 or p_3(b3) != 0 (are b's forced special?).
import sys, sympy as sp
t=sp.Symbol('t'); A=sp.symbols('a0:3'); B2=sp.symbols('c0:3'); B3=sp.symbols('d0:3')
for i in range(3):
    a=list(A)+[None]; a[i]=sp.Integer(1); a[3]=-(a[0]+a[1]+a[2]); b2=list(B2)+[-sum(B2)]; b3=list(B3)+[-sum(B3)]
    Y=sp.Matrix(4,5,lambda r,c: a[r]*[1,1,1,1,-2][c]+b2[r]*[0,0,1,0,-1][c]+b3[r]*[0,0,0,1,-1][c])
    C=[]
    for j in range(5):
        M=sp.Matrix(4,4,lambda r,c: 1+t*Y[r,[x for x in range(5) if x!=j][c]]); C.append(sp.expand(M.per()))
    eqs=[]
    for D in (C[1]-C[0],C[2]-C[0],C[3]-C[0],C[4]+4*C[0]-120):
        eqs+=[e for e in sp.Poly(sp.expand(D),t).all_coeffs() if e!=0]
    eqs+=[sp.expand(sum(x**2 for x in b2)),sp.expand(sum(x**2 for x in b3))]
    vs=[x for k,x in enumerate(A) if k!=i]+list(B2)+list(B3)
    p32='+'.join('(%s)^3'%str(x) for x in b2); p33='+'.join('(%s)^3'%str(x) for x in b3)
    with open('/home/kevxhk/work/L-gct-210/stage3/r14/shapeS2_%d.sing'%i,'w') as fh:
        fh.write('ring R=0,(%s,u),dp;\nideal I=%s;\nideal G=std(I);\n"S2 chart %d: dim",dim(G);\n'%(','.join(map(str,vs)),',\n'.join(str(e).replace('**','^') for e in eqs),i)
                 +'ideal G2=std(I+ideal(1-u*(%s)*(%s)));\n"S2 chart %d with p3(b2) p3(b3) != 0: dim",dim(G2);\nquit;\n'%(p32.replace('**','^'),p33.replace('**','^'),i))
    print('chart',i,'eqs',len(eqs),flush=True)
