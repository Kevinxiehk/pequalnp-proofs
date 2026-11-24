# verify2 r18: INDEPENDENT check of ncol THEOREM CC34 (no column-centred 3x4 level space of dim 4) -- own generator, exact over Q.
# Isotropic coordinates (a, b) in C^4 x C^4 (rows a w^k + b w^{2k}); level <=> P_2 = 3(a.b - AB) == 0 and P_3 = 6(e3(a)+e3(b)) == 0 on S (P_1 == 0).
# S in Gr(4,8): Pluecker charts (identity at the index set I), S4 x Z2 orbit representatives; Singular std over Q per chart.
import sympy as sp, itertools, subprocess
idx=list(range(8))  # 0..3 = a-columns, 4..7 = b-columns (column j <-> index j and 4+j)
def act(perm,swap,I):
    out=set()
    for x in I:
        col=x%4; side=x//4
        if swap: side=1-side
        out.add(side*4+perm[col])
    return frozenset(out)
seen=set(); reps=[]
for I in itertools.combinations(idx,4):
    I=frozenset(I)
    if I in seen: continue
    orb={act(p,s,I) for p in itertools.permutations(range(4)) for s in (0,1)}
    seen|=orb; reps.append(sorted(I))
print('orbits:',len(reps),reps)
lam=sp.symbols('l0:4')
e3=lambda v: sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(4),3))
res=[]
for I in reps:
    T=iter(sp.symbols('t0:16')); M=[]
    J=[c for c in idx if c not in I]
    for r in range(4):
        row=[0]*8; row[I[r]]=1
        for c in J: row[c]=next(T)
        M.append(row)
    s=[sum(lam[r]*M[r][c] for r in range(4)) for c in range(8)]
    a,b=s[:4],s[4:]
    P2=sp.expand(sum(x*y for x,y in zip(a,b))-sum(a)*sum(b)); P3=sp.expand(e3(a)+e3(b))
    eqs=sp.Poly(P2,*lam).coeffs()+sp.Poly(P3,*lam).coeffs()
    vs=sp.symbols('t0:16')
    open('cc34_%s.sing'%''.join(map(str,I)),'w').write('ring R=0,(%s),dp;\nideal E=%s;\nideal G=std(E); printf("CC34 chart %s over Q: #eqs %%s unit %%s",size(E),reduce(1,G)==0);\nquit;\n'%(','.join(map(str,vs)),','.join(str(e) for e in eqs),''.join(map(str,I))))
    r=subprocess.run('ulimit -v 1500000; timeout 600 Singular -q cc34_%s.sing'%''.join(map(str,I)),shell=True,capture_output=True,text=True)
    print(r.stdout.strip() or ('FAILED rc=%d %s'%(r.returncode,r.stderr[-100:])),flush=True)
