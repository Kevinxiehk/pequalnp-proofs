# verify2 r16: independent check of stage3's (PR3)/(PR2-split') counterexample (sec. 37 (E)). Own code: permanents over injections.
import sympy as sp, itertools
rho,b,c,d,s,r=sp.symbols('rho b c d s r')
xb=sp.Matrix([[-1,0,0,0,0],[1,1,-1,0,0],[0,0,0,0,0]]); xc=sp.Matrix([[-1,0,0,0,0],[0,0,0,0,0],[1,0,0,1,-1]])
xd=sp.Matrix([[1,0,0,0,0],[rho,0,0,0,0],[-1-rho,0,0,0,0]])
X=b*xb+c*xc+d*xd; z=sp.Matrix([[-2*s-2*r,s,s,r,r]]); N=X.col_join(z)
def perm_inj(M,cols):  # sum over injections rows -> cols of prod (1+M[i,f(i)])
    k=M.shape[0]; return sp.expand(sum(sp.prod([1+M[i,f[i]] for i in range(k)]) for f in itertools.permutations(cols,k)))
print('perm(J+X) 3x5 =',perm_inj(X,range(5)),'(level iff 60)')
print('perm(J+N) 4x5 =',perm_inj(N,range(5)),'(level iff 120)')
def defect(M,params,base):
    vecs=[]; Cj=[sp.expand(perm_inj(M,[q for q in range(5) if q!=j])-base) for j in range(5)]
    mons=set()
    for e in Cj: mons|=set(sp.Poly(e,*params).monoms()) if e!=0 else set()
    rows=[[sp.Poly(Cj[j],*params).coeff_monomial(m) if Cj[j]!=0 else 0 for j in range(5)] for m in mons]
    A=sp.Matrix(rows) if rows else sp.zeros(1,5); return A.rank(), A
for name,M,params,base in (('X',X,(b,c,d),24),('N',N,(b,c,d,s,r),24)):
    rk,A=defect(M,params,base); rs=A.rowspace(); print('defect of',name,'=',rk,' span:',[list(v) for v in rs][:3])
# dimension of N, row projections, single-row parts (generic rho; then rho = 1)
P=(b,c,d,s,r)
def lin(M): return sp.Matrix([[sp.diff(M[i,j],v) for i in range(M.shape[0]) for j in range(5)] for v in P])  # 5 x 20 basis
for rv in (rho,sp.Integer(1),sp.Integer(2)):
    B=lin(N).subs(rho,rv); print('rho =',rv,': dim N =',B.rank(),end='; ')
    proj=[B[:,5*i:5*i+5].rank() for i in range(4)]; print('row projection dims',proj,end='; ')
    sr=[]
    for i in range(4):
        other=sp.Matrix.hstack(*[B[:,5*k:5*k+5] for k in range(4) if k!=i])  # coefficient combos killing other rows
        ns=other.T.nullspace(); sr.append(len(ns))
    print('single-row part dims',sr)
for rv in (0,-1): B=lin(N).subs(rho,rv); print('degenerate rho =',rv,': single-row dims',[len(sp.Matrix.hstack(*[B[:,5*k:5*k+5] for k in range(4) if k!=i]).T.nullspace()) for i in range(4)])
