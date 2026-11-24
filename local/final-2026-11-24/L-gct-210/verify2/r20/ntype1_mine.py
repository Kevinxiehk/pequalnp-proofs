# verify2 r20: independent exact check of reg2's ntype1 (23.4): level, dim 6, dim T_1, rank q_Y at two Y, FO2 bound. Exact over Q(sqrt(-3)).
import sympy as sp, itertools
from sympy.polys.matrices import DomainMatrix
s3=sp.sqrt(-3); w=(-1+s3)/2; w2=sp.expand(-w-1); K=sp.QQ.algebraic_field(s3)
P=sp.symbols('p0:6')
def Zm(): return sp.zeros(5,5)
B=[]
Z=Zm(); Z[0,:4]=sp.Matrix([[0,1,w,w2]]); B.append(Z)
Z=Zm(); Z[3,:4]=sp.Matrix([[0,w2,1,w]]); B.append(Z)
Z=Zm(); Z[1,:]=sp.Matrix([[0,w,1,w2,0]]); Z[2,:]=-Z[1,:]; B.append(Z)
Z=Zm(); Z[0,0],Z[1,0],Z[2,0]=-2,1,1; B.append(Z)
Z=Zm(); Z[0,0],Z[3,0]=-1,1; B.append(Z)
Z=Zm(); Z[1,:]=sp.Matrix([[0,w+2,1-w,0,-1]]); Z[2,:]=sp.Matrix([[0,w2-1,w-1,0,1]]); B.append(Z)
Y=sum((P[k]*B[k] for k in range(6)),sp.zeros(5,5)); M=sp.ones(5,5)+Y
def perm(A):
    n=A.shape[0]; return sp.expand(sum(sp.prod([A[i,f[i]] for i in range(n)]) for f in itertools.permutations(range(n))))
lev=perm(M); print('perm(J+Y) - 120 simplifies to:',sp.simplify(lev-120))
print('dim M =',DomainMatrix.from_Matrix(sp.Matrix([list(b) for b in B]).applyfunc(sp.expand)).convert_to(K).rank())
cof={(i,j):perm(M.extract([k for k in range(5) if k!=i],[l for l in range(5) if l!=j])) for i in range(5) for j in range(5)}
mons=set()
for e in cof.values(): mons|=set(sp.Poly(e,*P).monoms())
A=sp.Matrix([[sp.expand(sp.Poly(cof[(i,j)],*P).coeff_monomial(m)) for i in range(5) for j in range(5)] for m in sorted(mons)])
dA=DomainMatrix.from_Matrix(A).convert_to(K); N=dA.nullspace().to_Matrix(); n=N.rows; print('dim T_1 =',n)
T=[sp.Matrix(5,5,list(N.row(a))) for a in range(n)]
for yv in ((1,2,-1,3,1,-2),(2,-1,1,1,-3,1),(3,1,2,-1,1,1)):
    Yv=sum((c*b for c,b in zip(yv,B)),sp.zeros(5,5)); A5=(sp.ones(5,5)+Yv).applyfunc(sp.expand)
    H={}
    for i,k in itertools.combinations(range(5),2):
        for j in range(5):
            for l in range(5):
                if j==l: continue
                rr=[r for r in range(5) if r not in (i,k)]; cc=[c for c in range(5) if c not in (j,l)]
                H[(i,j,k,l)]=sp.expand(perm(A5.extract(rr,cc)))
    G=sp.Matrix(n,n,lambda a,b: sp.expand(sum(h*(T[a][i,j]*T[b][k,l]+T[a][k,l]*T[b][i,j]) for (i,j,k,l),h in H.items())))
    rk=DomainMatrix.from_Matrix(G).convert_to(K).rank()
    print('Y =',yv,': rank q_Y on T_1 =',rk,' => FO2 bound (n - rk) + floor(rk/2) =',(n-rk)+rk//2)
