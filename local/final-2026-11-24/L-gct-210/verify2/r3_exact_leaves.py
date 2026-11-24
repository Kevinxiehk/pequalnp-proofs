# verify2: EXACT version of stage2's R3-1 leaf enumeration (exception triples), arithmetic in Q(i) throughout.
#  For every canonical configuration passing (E1) and every column triple S with ell != 0 on Pi~_S:
#   - the linear factors of the cubic c_S on K_S are proposed numerically, rationalised to Q(i) and VERIFIED exactly (c_S = 0 on ker l,
#     tested on the principal lattice |alpha| = 3 of a basis of ker l, which is unisolvent for cubic forms);
#   - COMPLETENESS of the factor list is certified exactly: 3 distinct factors (then c_S = k l1 l2 l3); or 1 factor with cofactor quadric of
#     rank >= 3 on ker l (irreducible); or 0 factors with a rational 3-dim section on which c_S is a SMOOTH plane cubic (Jacobian ideal
#     contains all quartics: exact rank 15), which excludes any linear factor (a reducible cubic is singular along a curve).
#   - the DFS over the branches "n**|K_S = 0" / "n**|K_S proportional to a factor" and the admissibility tests use exact ranks.
import sys, itertools, numpy as np, time
from fractions import Fraction as Fr
src=open('/home/kevxhk/work/L-gct-210/stage2/t10_typeII_exact.py').read().split("def typeII")[0]
exec(src)      # class G (Gaussian rationals), Z, ONE, I, nullspace(M,nc) -> (basis, rank), perm3
t0=time.time()
def gc(x): return complex(float(x.a),float(x.b))
def rank(M,nc):
    if not M: return 0
    return nullspace(M,nc)[1]
def dot(a,b):
    s=Z
    for x,y in zip(a,b): s=s+x*y
    return s
def typeII(cells,eps):
    w=[(I*eps) if q==0 else (ONE if q==1 else G(-1)) for q in cells]
    return w,[1 if q==2 else 0 for q in cells],[1 if q==1 else 0 for q in cells],G(Fr(-1,2),Fr(eps,2))
lat3=lambda n:[a for a in itertools.product(range(4),repeat=n) if sum(a)==3]
rng=np.random.default_rng(5)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def float_factors(cf,d):
    def T(a,b,c): return (cf(a+b+c)-cf(a+b)-cf(a+c)-cf(b+c)+cf(a)+cf(b)+cf(c))/6
    Ed=np.eye(d); scale=max(abs(cf(rnd(d))) for _ in range(6)); cands=[]
    if scale<1e-9: return None
    for trial in range(3):
        p=rnd(d); q=rnd(d); co=[cf(q),3*T(p,q,q),3*T(p,p,q),cf(p)]
        for s in np.roots(co):
            w=p+s*q; g=np.array([3*T(w,w,Ed[k]) for k in range(d)])
            if np.abs(g).max()>1e-6*scale: cands.append(g)
            else:
                H=np.array([[6*T(w,Ed[k],Ed[l]) for l in range(d)] for k in range(d)]); sv=np.linalg.svd(H); cands+= [sv[2][0].conj(),sv[2][0]]
    return cands
def rationalise(l):
    k=int(np.argmax(np.abs(l))); l=l/l[k]; out=[]
    for x in l:
        a=Fr(float(x.real)).limit_denominator(64); b=Fr(float(x.imag)).limit_denominator(64)
        if abs(float(a)-x.real)>1e-7 or abs(float(b)-x.imag)>1e-7: return None
        out.append(G(a,b))
    return out
STAT={'cubics':0,'ell=0':0,'3 factors':0,'1 factor + irreducible quadric':0,'0 factors, smooth section':0,'UNCERTIFIED':0,'irrational candidate':0}
def analyse(s12,s13):
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13)
    if not (A1==B1 or all(x+y==1 for x,y in zip(A1,B1))): return 'dimcount'
    def F(rows):
        v=[Z]*15
        for i,vec in rows:
            for j in range(5): v[5*i+j]=vec[j] if isinstance(vec[j],G) else G(vec[j])
        return v
    one=[1]*5
    A0=[F([(0,one),(1,[-1]*5)]),F([(0,one),(2,[-1]*5)]),F([(0,[G(A1[j])+y12 for j in range(5)]),(1,A2)]),F([(0,[G(B1[j])+y13 for j in range(5)]),(2,B3)])]
    u=[[ONE]*5,[x.inv() for x in w2],[x.inv() for x in w3]]; cons=[]
    for S in itertools.combinations(range(5),3):
        cols=[5*i+j for i in range(3) for j in S]
        Pt,_=nullspace([[r[c] for c in cols] for r in A0],9)
        ell=[v[0]+v[1]+v[2] for v in Pt]
        STAT['cubics']+=1
        if all(x.iszero() for x in ell): STAT['ell=0']+=1; continue
        comb,_=nullspace([ell],len(Pt)); E=[[dot(c,[v[k] for v in Pt]) for k in range(9)] for c in comb]; d=len(E)
        def cf(v):
            tau=[dot(v,[e[k] for e in E]) for k in range(9)]
            return perm3([[tau[3*i+k]*u[i][S[k]] for k in range(3)] for i in range(3)])
        Ef=np.array([[gc(x) for x in e] for e in E]); uf=np.array([[gc(u[i][j]) for j in S] for i in range(3)])
        def cff(v):
            A=(v@Ef).reshape(3,3)*uf
            return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]] for p in itertools.permutations(range(3)))
        cands=float_factors(cff,d); facs=[]
        if cands is None: return 'c=0 (unexpected)'
        for l in cands:
            r=rationalise(l)
            if r is None: continue
            if any(rank([r,f],d)==1 for f in facs): continue
            kb,_=nullspace([r],d)
            if all(cf([sum((kb[i][k]*a[i] for i in range(d-1)),Z) for k in range(d)]).iszero() for a in lat3(d-1)): facs.append(r)
        # completeness certificate
        def T(a,b,c):
            ad=lambda x,y:[p+q for p,q in zip(x,y)]
            return (cf(ad(ad(a,b),c))-cf(ad(a,b))-cf(ad(a,c))-cf(ad(b,c))+cf(a)+cf(b)+cf(c))/6
        ok=False
        if len(facs)==3: ok=True; STAT['3 factors']+=1
        elif len(facs)==1:
            l=facs[0]; kb,_=nullspace([l],d); k0=next(k for k in range(d) if not l[k].iszero()); w=[Z]*d; w[k0]=l[k0].inv()
            Gm=[[T(kb[i],kb[j],w) for j in range(d-1)] for i in range(d-1)]
            if rank(Gm,d-1)>=3: ok=True; STAT['1 factor + irreducible quadric']+=1
        elif len(facs)==0 and d>=3:
            ev=[[ONE if k==i else Z for k in range(d)] for i in range(d)]
            for trip in list(itertools.combinations(range(d),3))+[None]:
                if trip is None: b=[[G(1),G(1),G(0),G(2)][:d]+[Z]*(d-4),[G(0),G(1),G(1),G(-1)][:d]+[Z]*(d-4),[G(1),G(0),G(2),G(1)][:d]+[Z]*(d-4)]
                else: b=[ev[i] for i in trip]
                # plane cubic g(x) = c(x1 b1 + x2 b2 + x3 b3): coefficients by monomial
                mon3=lat3(3); coef={}
                for a in mon3:
                    idx=[i for i in range(3) for _ in range(a[i])]; mult={1:1,2:3,3:6}[len(set(idx))] if len(set(idx))!=2 else 3
                    coef[a]=T(b[idx[0]],b[idx[1]],b[idx[2]])*mult
                mon2=[a for a in itertools.product(range(3),repeat=3) if sum(a)==2]; mon4=[a for a in itertools.product(range(5),repeat=3) if sum(a)==4]; i4={a:k for k,a in enumerate(mon4)}
                rows=[]
                for i in range(3):
                    part={}
                    for a,c in coef.items():
                        if a[i]>0:
                            bb=list(a); bb[i]-=1; part[tuple(bb)]=c*a[i]
                    for m in mon2:
                        row=[Z]*15
                        for a,c in part.items(): row[i4[tuple(x+y for x,y in zip(a,m))]]=c
                        rows.append(row)
                if rank(rows,15)==15: ok=True; STAT['0 factors, smooth section']+=1; break
        if not ok: STAT['UNCERTIFIED']+=1
        Rv=[]
        for e in E:
            r=[Z]*10
            for k,j in enumerate(S): r[j]=e[3+k]; r[5+j]=e[6+k]
            Rv.append(r)
        cons.append((Rv,facs,d))
    def inB(m,vecs,lo): 
        part=m[lo:lo+5]; base=[[G(x) for x in v] for v in vecs]
        return rank(base+[part],5)==rank(base,5)
    def adm(V): return V and not all(inB(m,[one,B3],5) for m in V) and not all(inB(m,[one,A2],0) for m in V)
    def cut(V,conds):
        if not V: return V
        M=[[dot(c,v) for v in V] for c in conds]; ns,_=nullspace(M,len(V))
        return [[dot(c,[v[k] for v in V]) for k in range(10)] for c in ns]
    leaves=[]
    def dfs(idx,V):
        if not adm(V): return
        if idx==len(cons): leaves.append(V); return
        Rv,facs,d=cons[idx]
        dfs(idx+1,cut(V,Rv))
        for lam in facs:
            pk,_=nullspace([lam],d)
            dfs(idx+1,cut(V,[[dot(p,[r[k] for r in Rv]) for k in range(10)] for p in pk]))
    dfs(0,[[ONE if k==i else Z for k in range(10)] for i in range(10)])
    return ('SURVIVES',leaves,(A1,A2,B1,B3)) if leaves else ('killed',)

def rref_basis(V):
    M=[list(v) for v in V]; r=0; piv=[]
    for c in range(10):
        p=next((i for i in range(r,len(M)) if not M[i][c].iszero()),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c].inv(); M[r]=[x*pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and not M[i][c].iszero():
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        r+=1
        if r==len(M): break
    return M[:r]
def contains(W,V): return rank(W+V,10)==len(W)
def vec(m2,m3): return [x if isinstance(x,G) else G(x) for x in list(m2)+list(m3)]
SURV=[((0,1,2,2,2),(0,1,2,2,2),-1),((0,1,1,1,2),(0,1,1,1,2),-1),((0,0,0,1,2),(0,0,0,1,2),-1),((0,0,0,1,2),(0,1,1,0,2),1),((0,0,0,1,2),(1,0,1,0,2),1),
      ((0,0,0,1,2),(1,1,0,0,2),1),((0,1,1,2,2),(0,1,1,2,2),-1),((0,0,1,2,2),(0,0,1,2,2),-1),((0,0,1,1,2),(0,0,1,1,2),-1),((0,0,1,1,2),(0,1,0,0,2),1),
      ((0,0,1,1,2),(1,0,0,0,2),1),((0,0,1,1,2),(1,1,0,0,2),1)]
which=[int(x) for x in sys.argv[1:]] if len(sys.argv)>1 else range(12)
for k in which:
    c12,c13,eps=SURV[k]
    r=analyse((c12,1),(c13,eps)); leaves=r[1]; A1,A2,B1,B3=r[2]
    leaves=[rref_basis(V) for V in leaves]; leaves.sort(key=lambda V:-len(V)); mx=[]
    for V in leaves:
        if not any(contains(W,V) for W in mx): mx.append(V)
    Q1=[1 if q==0 else 0 for q in c12]; Q1p=[1 if q==0 else 0 for q in c13]; z5=[0]*5; one=[1]*5
    base=[vec(one,z5),vec(z5,one),vec(A2,[-x for x in B3])]            # f_2, f_3, G_12 - G_13 (mod ell)
    if eps==-1:                                                        # conjugate family (a)
        fam=base+[vec([G(Q1[j])+G(1,-1)*A2[j] for j in range(5)],[G(0,-1)*Q1[j] for j in range(5)])]; name='(a) conjugate'
    else:
        e=lambda j:[1 if t==j else 0 for t in range(5)]
        Q2=[j for j in range(5) if A2[j]]; Q2p=[j for j in range(5) if B3[j]]
        if len(Q2)==1 and len(Q2p)==2:      # A: Q_2' = {j1,j2} inside Q_1, Q_1' = {j0} + Q_2
            j0=[j for j in range(5) if Q1[j] and j not in Q2p][0]
            fam=base+[vec(e(j0),z5),vec(z5,[a-b for a,b in zip(e(Q2p[0]),e(Q2p[1]))]),vec(e(Q2[0]),z5)]; name='(b) type A'
        elif len(Q2)==2 and len(Q2p)==1:    # B: mirror image
            j0=[j for j in range(5) if Q1p[j] and j not in Q2][0]
            fam=base+[vec(z5,e(j0)),vec([a-b for a,b in zip(e(Q2[0]),e(Q2[1]))],z5),vec(z5,e(Q2p[0]))]; name='(b) type B'
        else:                               # C: Q_1 = Q_2', Q_2 = Q_1'
            fam=base+[vec([a-b for a,b in zip(e(Q2[1]),e(Q2[0]))],z5),vec(z5,[a-b for a,b in zip(e(Q2p[0]),e(Q2p[1]))]),vec([a+b for a,b in zip(e(Q2[0]),e(Q2[1]))],z5)]; name='(b) type C'
    print(c12,c13,eps,': leaves',len(leaves),' distinct maximal leaves',len(mx),' dims',[len(V) for V in mx],'; claimed family',name,'dim',rank(fam,10),
          ' equals the maximal leaf:',[len(V)==rank(fam,10) and contains(V,fam) for V in mx],flush=True)
