# verify2 r8: (T2) for (S3) with sg SYMBOLIC: consistency of the linear system over Q(sg); exceptional sg = where ranks drop.
import sys, itertools, sympy as sp
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2/r8')
sg=sp.Symbol('sg')
NV=5
def basis():
    B=[]
    M=[[sp.Integer(0)]*5 for _ in range(4)]; col=[sg,-1-sg,0,1]
    for i in range(4): M[i][0]=col[i]
    B.append(M)
    for row,w in ((2,(-4,1,1,1,1)),(2,(0,1,-1,0,0)),(3,(0,0,0,1,-1)),(3,(0,1,1,-1,-1))):
        M=[[sp.Integer(0)]*5 for _ in range(4)]; M[row]=[sp.Integer(x) for x in w]; B.append(M)
    return B
c=sp.symbols('c0:5'); B=basis()
X=[[sum(c[q]*B[q][i][l] for q in range(5)) for l in range(5)] for i in range(4)]
def perm(M):
    n=len(M); return sp.expand(sum(sp.prod([M[i][s[i]] for i in range(n)]) for s in itertools.permutations(range(n))))
D=[[[0 if l==j else perm([[X[a][cc] for cc in range(5) if cc not in (j,l)] for a in range(4) if a!=i]) for l in range(5)] for i in range(4)] for j in range(5)]
T=sp.symbols('T0:100'); d=sp.symbols('d0:5')
eqs=[]
for j in range(5):
    for k in range(j,5):
        expr=sum(T[k*20+i*5+l]*D[j][i][l]+T[j*20+i*5+l]*D[k][i][l] for i in range(4) for l in range(5))
        P=sp.Poly(sp.expand(expr),*c)
        eqs+= [cf for cf in P.coeffs()]
for i in range(4):
    for l in range(5):
        eqs.append(sum(T[k*20+i*5+l] for k in range(5))+sum(d[q]*B[q][i][l] for q in range(5))-1)
unk=list(T)+list(d)
A,bvec=sp.linear_eq_to_matrix(eqs,unk)
print('system',A.shape,flush=True)
Aug=A.row_join(bvec)
# generic ranks over Q(sg) via fraction-free elimination on sympy matrices
rA=A.rank(simplify=True); rAug=Aug.rank(simplify=True)
print('generic rank coef',rA,'aug',rAug,flush=True)
# witness: left null vector y of A with y.b != 0 -> exceptional sg are zeros of y.b (after clearing denominators) and poles
ns=(A.T).nullspace(simplify=True)
vals=[sp.factor(sp.simplify((y.T*bvec)[0])) for y in ns]
print('number of left null vectors',len(ns),flush=True)
for v in vals:
    if v!=0: print('y.b =',v)
for y in ns:
    v=sp.simplify((y.T*bvec)[0])
    if v!=0:
        dens=set(sp.factor(sp.denom(sp.together(e))) for e in y if e!=0)
        chk=sp.simplify(y.T*A)
        print('witness: denominators',dens,' y^T A == 0:',all(sp.simplify(e)==0 for e in chk))
        break
