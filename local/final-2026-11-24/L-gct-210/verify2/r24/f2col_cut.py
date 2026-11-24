# verify2 r24: independent re-implementation of stage2's symmetry cuts (F2COL-TABLE rows 3, 10, 12, 14, 16, 17, 20-cut).
# Points n = (a1:a2:a3:a4) in P^3 (Z-normal, column-0 entry 0). Survivor superset S = {n : for all g in G with g(n)_4 != 0, g(n) in X},
# X = union of linear pieces (hyperplanes / points, homogeneous). Stratify by the zero set Zs of n; on each stratum the chart condition is fixed.
# Output: maximal linear subspaces L (projective) with L meeting the open stratum.  Exact rational arithmetic (sympy).
import itertools, sys, sympy as sp
def rref_key(M):
    if M.rows==0: return ()
    R,piv=M.rref(); R=R[:len(piv),:]
    return tuple(tuple(R.row(i)) for i in range(R.rows))
def mat(rows): return sp.Matrix(rows) if rows else sp.zeros(0,4)
def dimP(M): return 3-(M.rank() if M.rows else 0)   # projective dimension (-1 = empty)
def hyp(c): return [list(map(sp.Rational,c))]
def pt(p):  # equations of a point: complement of its span
    v=sp.Matrix([list(map(sp.Rational,p))]); N=v.nullspace(); return [list(x.T) for x in N]
def act(eqs,perm):  # perm: g(n)_i = n_{perm[i]}; equation c.g(n) = sum_j c_{perm^-1 j} n_j
    inv={perm[i]:i for i in range(4)}
    return [[e[inv[j]] for j in range(4)] for e in eqs]
def contained(K1,K2):  # L(K1) subset L(K2) ?
    M1=mat(list(K1)); M2=mat(list(K1)+list(K2)); return M2.rank()==M1.rank()
def cut(X,G,Zs,extra=[]):
    base=[[1 if j==k else 0 for j in range(4)] for k in Zs]+extra
    nz=[k for k in range(4) if k not in Zs]
    def alive(K):
        M=mat(list(K))
        if dimP(M)<0: return False
        for k in nz:  # L must not lie in {a_k = 0}
            e=[1 if j==k else 0 for j in range(4)]
            if mat(list(K)+[e]).rank()==M.rank(): return False
        return True
    cur={rref_key(mat(base))} if base else {()}
    cur={k for k in cur if alive(k)}
    for g in G:
        if g[3] in Zs: continue          # g(n)_4 = n_{g[3]} = 0: not in the chart, no condition
        nxt=set()
        for K in cur:
            for P in X:
                K2=rref_key(mat(list(K)+act(P,g)))
                if alive(K2): nxt.add(K2)
        # keep maximal
        cur={K for K in nxt if not any(K!=K2 and contained(K,K2) for K2 in nxt)}
    return cur
def show(K):
    M=mat(list(K)); d=dimP(M)
    if d==0:
        v=M.nullspace()[0]; v=list(v.T)
        if v[3]!=0: v=[x/v[3] for x in v]
        return 'POINT '+str(tuple(v))
    return 'dim %d: '%d+' ; '.join(str(sp.expand(sum(c*s for c,s in zip(row,sp.symbols('a1 a2 a3 a4')))))+'=0' for row in K)
S3=[(0,)+tuple(p) for p in itertools.permutations((1,2,3))]
S4=[tuple(p) for p in itertools.permutations((0,1,2,3))]
def run(name,X,G,strata,extra=[]):
    print('=====',name,flush=True)
    for Zs in strata:
        res=cut(X,G,Zs,extra)
        print('  zero set',[z+1 for z in Zs],':',len(res),'components',flush=True)
        for K in sorted(res,key=lambda k:(len(k),str(k))): print('     ',show(K))
H=hyp((1,2,2,-6)); A=hyp((1,0,0,0)); D=hyp((1,1,1,-4)); J=hyp((1,1,1,1))
P01=[pt((x,y,z,1)) for x in (0,1) for y in (0,1) for z in (0,1)]
