# Round 14: the special-W enumeration of sec. 33 (F)-(G) EXACTLY over F_P (P = 2147483629, i = sqrt(-1) mod P).
# For every 4-tuple of special lines (row permutations of chi_1): kernel of sum l_j v_j = 0 (exact mod P); if the kernel is 1-dim: test
# all l_j != 0, all four triple moments tau = 0, perm(W) = 0.  Kernel dim >= 2 only for repeated lines: patterns (p,p,q,q) tested
# symbolically (tau(v,v,w) = tau(v,w,w) = 0 and <v,w>^2 = 3 sum v^2 w^2), (p,p,q,r) / (p,p,p,q) / (p,p,p,p) excluded by hand (sec. 33 (G)).
import itertools
P=2147483629
g=next(x for x in range(2,1000) if pow(x,(P-1)//2,P)==P-1); I=pow(g,(P-1)//4,P)
base=[1,I,P-1,P-I]
def normalize(v):
    k=next(x for x in v if x%P); inv=pow(k,P-2,P); return tuple(x*inv%P for x in v)
lines=sorted({normalize([base[k] for k in p]) for p in itertools.permutations(range(4))})
print('special lines mod P:',len(lines))
def nullspace(cols):   # columns cols (4 vectors in F_P^4): kernel of the 4x4 matrix M with M[r][j] = cols[j][r]
    M=[[cols[j][r]%P for j in range(4)] for r in range(4)]; piv=[]; R=[row[:] for row in M]; r=0
    for c in range(4):
        pr=next((k for k in range(r,4) if R[k][c]),None)
        if pr is None: continue
        R[r],R[pr]=R[pr],R[r]; inv=pow(R[r][c],P-2,P); R[r]=[x*inv%P for x in R[r]]
        for k in range(4):
            if k!=r and R[k][c]: f=R[k][c]; R[k]=[(a-f*b)%P for a,b in zip(R[k],R[r])]
        piv.append(c); r+=1
    free=[c for c in range(4) if c not in piv]; basis=[]
    for fc in free:
        v=[0]*4; v[fc]=1
        for k,pc in enumerate(piv): v[pc]=(-R[k][fc])%P
        basis.append(v)
    return basis
def perm4(W):
    return sum(W[0][p[0]]*W[1][p[1]]*W[2][p[2]]*W[3][p[3]] for p in itertools.permutations(range(4)))%P
found=[]; multi=0
for combo in itertools.product(range(len(lines)),repeat=4):
    cols=[lines[c] for c in combo]; ns=nullspace(cols)
    if len(ns)!=1: multi+=1; continue
    lam=ns[0]
    if any(x%P==0 for x in lam): continue
    W=[[cols[j][r]*lam[j]%P for j in range(4)] for r in range(4)]
    taus=[sum(W[r][a]*W[r][b]*W[r][c] for r in range(4))%P for a,b,c in itertools.combinations(range(4),3)]
    if all(x==0 for x in taus) and perm4(W)==0: found.append(combo)
sets=sorted({tuple(sorted(c)) for c in found})
print('4-tuples with 1-dim kernel passing all conditions:',len(found),' as sets of lines:',sets,' (tuples with kernel dim >= 2:',multi,')')
bad=0
for a,b in itertools.permutations(range(len(lines)),2):
    v,w=lines[a],lines[b]
    t1=sum(v[r]*v[r]*w[r] for r in range(4))%P; t2=sum(v[r]*w[r]*w[r] for r in range(4))%P
    pw=(sum(v[r]*w[r] for r in range(4))**2-3*sum(v[r]**2*w[r]**2 for r in range(4)))%P
    if t1==0 and t2==0 and pw==0: bad+=1
print('(p,p,q,q) survivors mod P:',bad)
# omitted pairs of the surviving sets (should be the 3 opposite pairs)
for s_ in sets: print('  set',s_,'omits',tuple(x for x in range(6) if x not in s_))
