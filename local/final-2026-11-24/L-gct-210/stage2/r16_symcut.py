# S_3-symmetry cut [NOTES-stage2 R16-5]: FO2-joint survival is invariant under permutations of columns 2,3,4, which act on the Z-normal
# n = (a1, a2, a3, a4) (column 0 coordinate normalised to 0) by permuting (a2, a3, a4), with P (columns 0,1) and nu fixed. If the kernel kill gives
# survivors in the chart a4 = 1 inside X = H u A u D u Pts (H: a1+2a2+2a3 = 6 a4, A: a1 = 0, D: a1+a2+a3 = 4 a4, Pts: the 0/1 points), then a
# survivor n with a2 a3 a4 != 0 (all sigma(n) in the chart) lies in  INTERSECTION over sigma of sigma^{-1}(X). Linear algebra over Q (projective n).
import itertools, sympy as sp
a=sp.symbols('a1:5')
H=[a[0]+2*a[1]+2*a[2]-6*a[3]]; A=[a[0]]; D=[a[0]+a[1]+a[2]-4*a[3]]
pts=[(1,0,0,1),(1,0,1,1),(1,1,0,1),(1,1,1,1)]
def ptlin(p):   # linear equations of the projective point p: all 2x2 minors of [n; p]
    return [a[i]*p[j]-a[j]*p[i] for i in range(4) for j in range(i+1,4)]
pieces={'H':H,'A':A,'D':D}
for k,p in enumerate(pts): pieces['P%d'%k]=ptlin(p)
perms=list(itertools.permutations([1,2,3]))
def act(eqs,s):   # sigma^{-1}(X): substitute a_{pos} -> a_{s(pos)}
    sub={a[0]:a[0]}; 
    for i,j in zip([1,2,3],s): sub[a[i]]=a[j]
    return [e.xreplace(sub) for e in eqs]
res=set()
def dfs(k,eqs):
    if eqs:
        M=sp.Matrix([[sp.Poly(e,*a).coeff_monomial(v) for v in a] for e in eqs]); r=M.rank()
        if r==4: return
        if k==len(perms):
            ns=M.nullspace(); res.add((3-r,str(sorted([list(v) for v in sp.Matrix.hstack(*ns).T.rref()[0].tolist()])))); return
    elif k==len(perms): return
    for c in pieces: dfs(k+1,eqs+act(pieces[c],perms[k]))
dfs(0,[])
print('projective components of the symmetric cut (dim, rref basis of the span of n):')
for d,v in sorted(res): print('  dim',d,':',v)
