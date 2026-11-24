# Round 11: EXACT certificate for one rational member of the jump locus H: w2 = e4 - e1, w3 = (0,1,1,-3,1) (w2 o w3 = w2).
# T_1(N) exactly (integer linear algebra over Q via sympy), the forms q_m on V = T_1/N at integer points m, their span, and a Singular
# script computing the dimension of the common null cone K (homogeneous ideal of the forms in the 8 coordinates of V).
import itertools, random, sympy as sp
random.seed(1)
import sys
w2=[sp.Rational(t) for t in sys.argv[1].split(',')]; w3=[sp.Rational(t) for t in sys.argv[2].split(',')]; TAG=sys.argv[3]
B=[]
for (i,k) in ((0,1),(1,2),(2,3)):
    M=[[0]*5 for _ in range(5)]; M[i][0]=1; M[k][0]=-1; B.append(M)
M=[[0]*5 for _ in range(5)]; M[2]=list(w2); B.append(M); M=[[0]*5 for _ in range(5)]; M[3]=list(w3); B.append(M)
P4=list(itertools.permutations(range(4))); P3=list(itertools.permutations(range(3)))
def perm(A,P):
    n=len(A); return sum(sp.prod([A[i][p[i]] for i in range(n)]) for p in P)
def point():
    c=[random.randint(-6,6) for _ in range(5)]
    return [[1+sum(c[k]*B[k][i][j] for k in range(5)) for j in range(5)] for i in range(5)]
def cof(U): return [perm([[U[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i],P4) for i in range(5) for j in range(5)]
def hess(U):
    H=[[0]*25 for _ in range(25)]
    for i,k in itertools.permutations(range(5),2):
        rr=[x for x in range(5) if x not in (i,k)]
        for j,l in itertools.permutations(range(5),2):
            cc=[x for x in range(5) if x not in (j,l)]; H[5*i+j][5*k+l]=perm([[U[a][b] for b in cc] for a in rr],P3)
    return sp.Matrix(H)
# level check (exact) at random integer points
assert all(perm(point(),list(itertools.permutations(range(5))))==120 for _ in range(30)), 'not level'
A=sp.Matrix([cof(point()) for _ in range(160)]); ns=A.nullspace(); n=len(ns); print('dim T_1 =',n,flush=True)
T=sp.Matrix.hstack(*ns)                                       # 25 x n
Bv=sp.Matrix([[B[k][i][j] for k in range(5)] for i in range(5) for j in range(5)])   # 25 x 5
X=(T.T*T).solve(T.T*Bv)                                        # coords of N in T (exact, T full column rank)
assert T*X==Bv, 'N not inside T_1'
# complement: extend X (n x 5) by unit vectors to a basis of Q^n
cols=list(X.T.tolist()); comp=[]
for e in range(n):
    v=[0]*n; v[e]=1
    if sp.Matrix(cols+[v]).rank()>len(cols): cols.append(v); comp.append(v)
Vb=T*sp.Matrix(comp).T; m=Vb.shape[1]; print('dim V =',m,flush=True)
forms=[]; vecs=[]
for _ in range(45):
    G=(Vb.T*hess(point())*Vb); forms.append(G); vecs.append([G[a,b] for a in range(m) for b in range(a,m)])
Mx=sp.Matrix(vecs); r=Mx.rank(); print('span of forms on V: dim',r,flush=True)
basis=[]; cur=[]
for G,v in zip(forms,vecs):
    if sp.Matrix(cur+[v]).rank()>len(cur): cur.append(v); basis.append(G)
    if len(basis)==r: break
xs=sp.symbols('x0:%d'%m); xv=sp.Matrix(xs)
polys=[sp.expand((xv.T*G*xv)[0]) for G in basis]
den=1
for P_ in polys:
    for c in sp.Poly(P_,*xs).coeffs(): den=sp.ilcm(den,sp.fraction(sp.nsimplify(c))[1])
polys=[sp.expand(P_*den) for P_ in polys]
with open('/home/kevxhk/work/L-gct-210/stage3/r11/ncdef_cone_exact_%s.sing'%TAG+'','w') as f:
    f.write('ring r=0,(%s),dp;\nideal I=%s;\nideal G=std(I);\n"KRULL_DIM",dim(G);\n"N_GENERATORS",size(G);\nquit;\n'%(','.join(map(str,xs)),',\n'.join(str(P_).replace('**','^') for P_ in polys)))
print('Singular script written',flush=True)
