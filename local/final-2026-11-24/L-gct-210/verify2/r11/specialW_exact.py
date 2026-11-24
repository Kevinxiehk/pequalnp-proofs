# verify2 r11: EXACT (sympy, Q(i)) redo of stage3 special_W.py + the hand repetition cases of 33(G)
import sympy as sp, itertools
I=sp.I
base=[1,I,-1,-I]; lines=[]
for p in itertools.permutations(range(4)):
    v=sp.Matrix([base[k] for k in p])
    if not any(sp.Matrix.hstack(v,w).rank(simplify=True)<2 for w in lines): lines.append(v)
print('special lines:',len(lines), ' isotropic:',all(sp.expand((v.T*v)[0])==0 for v in lines),' p3 = 0:',all(sp.expand(sum(x**3 for x in v))==0 for v in lines))
P4=list(itertools.permutations(range(4)))
def perm(W): return sp.expand(sum(sp.prod([W[r,q[r]] for r in range(4)]) for q in P4))
found=[]
for S in itertools.combinations(range(6),4):
    V=sp.Matrix.hstack(*[lines[c] for c in S]); ns=V.nullspace()
    assert len(ns)==1
    lam=[sp.nsimplify(sp.expand(x)) for x in ns[0]]
    if any(sp.expand(x)==0 for x in lam): print(S,'some lambda = 0'); continue
    W=V*sp.diag(*lam)
    taus=[sp.expand(sum(W[r,a]*W[r,b]*W[r,c] for r in range(4))) for a,b,c in itertools.combinations(range(4),3)]
    pm=perm(W)
    ok=all(t==0 for t in taus) and pm==0
    print('lines',S,'lambda',lam,'taus zero',[t==0 for t in taus],'perm',sp.simplify(pm),'-> CANDIDATE' if ok else '')
    if ok: found.append(S)
print('candidates (distinct lines):',found)
# (p,p,q,q): need tau(v,v,w) = tau(v,w,w) = 0 and <v,w>^2 = 3 sum v^2 w^2
bad=[]
for a,b in itertools.permutations(range(6),2):
    v,w=lines[a],lines[b]
    t1=sp.expand(sum(v[r]**2*w[r] for r in range(4))); t2=sp.expand(sum(v[r]*w[r]**2 for r in range(4)))
    c=sp.expand((v.T*w)[0]**2-3*sum(v[r]**2*w[r]**2 for r in range(4)))
    if t1==0 and t2==0 and c==0: bad.append((a,b))
print('(p,p,q,q) pairs satisfying all three:',bad)
