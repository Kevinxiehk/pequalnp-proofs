# EXACT treatment of the special locus of pattern (2,1,1|2) case (ii) (reg2 round 3).
#  (D)  disjoint supports: b = e_1 - e_2, c = e_3 - e_4, a = e_1 + e_2 - e_3 - e_4 (one orbit): Fraction certificate (exact_fo2.cert).
#  (S4) common zero column 4: b = (b1,b2,b3,0) in H, c = b x (1,1,1) = (b2-b3, b3-b1, b1-b2, 0), a = (1,1,1,-3); chart b = (1, s, -1-s, 0)
#       and the point b = (0,1,-1,0).  Symbolic over Q(s) with sympy: generic rank of the FO matrix A(s) (dim T_1 = 25 - rank),
#       gcd of maximal minors (where dim T_1 could jump), and gcd of 3x3 minors of q_Y restricted to a polynomial basis of ker A(s).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import itertools, sympy as sp
from fractions import Fraction as Fr
s=sp.symbols('s'); ys=sp.symbols('y1:7')
def perm(M):
    n=M.shape[0]
    return sp.Add(*[sp.Mul(*[M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))])
def basis(a,b,c):
    Z=lambda: sp.zeros(4,5)
    B1=Z(); B1[0,:]=sp.Matrix([[4,-1,-1,-1,-1]])
    B2=Z(); B3=Z(); B4=Z()
    for j in range(4): B2[0,1+j]=a[j]; B3[1,1+j]=b[j]; B4[2,1+j]=c[j]
    B5=Z(); B5[1,0]=1; B5[2,0]=-1
    B6=Z(); B6[2,0]=1; B6[3,0]=-1
    return [B1,B2,B3,B4,B5,B6]
def bigY(B):
    Y=sp.zeros(5,5)
    for k in range(6): Y[:4,:]+=ys[k]*B[k]
    return Y
def fo_matrix(B):
    A=sp.ones(5,5)+bigY(B); rows={}
    for i in range(5):
        for j in range(5):
            m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
            for mon,cf in P.terms():
                rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
    return sp.Matrix([r for r in rows.values()])
def hessian(B,yv):
    A=sp.ones(5,5)+bigY(B).subs(dict(zip(ys,yv))); H=sp.zeros(25,25)
    for i in range(5):
        for k in range(i+1,5):
            for j in range(5):
                for l in range(5):
                    if j==l: continue
                    m=A.copy(); m.row_del(k); m.row_del(i);
                    cols=[cc for cc in range(5) if cc not in (j,l)]; m=m[:,cols]
                    v=sp.expand(perm(m)); H[5*i+j,5*k+l]=v; H[5*k+l,5*i+j]=v
    return H
if __name__=='__main__':
    which=sys.argv[1] if len(sys.argv)>1 else 'S4'
    if which=='S4':
        b=[1,s,-1-s,0]; c=[b[1]-b[2],b[2]-b[0],b[0]-b[1],0]; a=[1,1,1,-3]
    elif which=='S4pt':
        b=[0,1,-1,0]; c=[b[1]-b[2],b[2]-b[0],b[0]-b[1],0]; a=[1,1,1,-3]
    elif which=='pt':
        v=[sp.Rational(x) for x in sys.argv[2].split(',')]; b=v[0:4]; c=v[4:8]; a=v[8:12]
    elif which=='D':
        b=[1,-1,0,0]; c=[0,0,1,-1]; a=[1,1,-1,-1]
    B=basis(a,b,c)
    # level check (symbolic, exact): F(J'+Y) - 120 == 0
    A5=sp.ones(5,5)+bigY(B); lev=sp.expand(perm(A5)-120); print(which,'level identity:',lev==0,flush=True)
    A=fo_matrix(B); print('FO matrix',A.shape,flush=True)
    dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(sp.QQ.frac_field(s) if which=='S4' else sp.QQ)
    rk=dm.rank(); print('generic rank',rk,'=> dim T_1 =',25-rk,flush=True)
    N=dm.nullspace().to_Matrix()       # rows = basis of ker
    # clear denominators row-wise
    Nrows=[]
    for r in range(N.shape[0]):
        row=[sp.together(x) for x in N.row(r)]; den=sp.lcm([sp.denom(x) for x in row]); Nrows.append([sp.expand(sp.cancel(x*den)) for x in row])
    N=sp.Matrix(Nrows); print('kernel basis',N.shape,' A*N^T == 0:',sp.simplify(A*N.T)==sp.zeros(A.shape[0],N.shape[0]),flush=True)
    if which=='S4' and 'minors' in sys.argv:
        # where can rank A drop?  gcd of some maximal minors (pivot rows/cols from the generic rref)
        _,piv=A.subs(s,sp.Rational(7,3)).rref(); piv=list(piv)
        # choose rows: greedy independent rows at s = 7/3
        As=A.subs(s,sp.Rational(7,3)); rows=[]; cur=sp.zeros(0,25)
        for r in range(A.shape[0]):
            t=cur.col_join(As.row(r))
            if t.rank()>cur.rank(): rows.append(r); cur=t
            if len(rows)==rk: break
        g=None; cnt=0
        for cols in itertools.combinations(range(25),rk):
            sub=A.extract(rows,list(cols)); d=sp.factor(sub.det(method='berkowitz'))
            if d==0: continue
            g=d if g is None else sp.gcd(g,d); cnt+=1
            print('  minor',cnt,'gcd so far:',sp.factor(g),flush=True)
            if sp.degree(g,s)==0 or cnt>=12: break
        print('gcd of maximal minors (subset):',sp.factor(g))
    if which=='S4':
        # rank of q on span(N)
        G=None
        for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1),(1,1,1,1,1,1)]:
            H=hessian(B,yv); Q=sp.expand(N*H*N.T)
            for idx in itertools.combinations(range(N.shape[0]),3):
                for jdx in [idx]:
                    d=sp.expand(Q.extract(list(idx),list(jdx)).det(method='berkowitz'))
                    if d==0: continue
                    G=d if G is None else sp.gcd(G,d)
                    if sp.degree(G,s)<=0: break
                if G is not None and sp.degree(G,s)<=0: break
            print('  y =',yv,' gcd of principal 3x3 minors of q on ker A(s):',sp.factor(G),flush=True)
            if G is not None and sp.degree(G,s)<=0: break
    else:
        best=0
        for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
            H=hessian(B,yv); Q=N*H*N.T; best=max(best,Q.rank())
        print('rank q on ker A:',best,' => dim L <=',N.shape[0]-(best+1)//2)
