# verify2: second stage of the exact structured search for N3' (see n3p_struct.py).
import itertools, numpy as np, sys, pickle, time
from fractions import Fraction as Fr
t0=time.time()
spans=pickle.load(open('/home/kevxhk/work/L-gct-210/verify2/n3p_spans.pkl','rb'))
P3=list(itertools.permutations(range(3)))
def F(r1,r2,r3): return sum(r1[p[0]]*r2[p[1]]*r3[p[2]] for p in P3)
def rows(v): return [v[0:3],v[3:6],v[6:9]]
E9=[[Fr(1) if k==c else Fr(0) for k in range(9)] for c in range(9)]
def DD(v,w):
    """linear functional b -> D_v D_w perm(b) as a 9-vector"""
    V=rows(v); W=rows(w); out=[]
    for c in range(9):
        B=rows(E9[c]); s=0
        for r,sx in itertools.permutations(range(3),2):
            t=[None]*3; t[r]=V[r]; t[sx]=W[sx]; o=3-r-sx; t[o]=B[o]; s+=F(*t)
        out.append(s)
    return out
def D(v,b,b2):
    """bilinear: polarisation of b -> D_v perm(b) : sum over rows r: F(v_r, b_s, b2_t) symmetrised"""
    V=rows(v); B=rows(b); B2=rows(b2); s=0
    for r in range(3):
        o=[x for x in range(3) if x!=r]
        for (x,y) in ((o[0],o[1]),(o[1],o[0])):
            t=[None]*3; t[r]=V[r]; t[x]=B[x]; t[y]=B2[y]; s+=F(*t)
    return s/2
def rref(M,nc):
    M=[list(r) for r in M]; piv=[]; r=0
    for c in range(nc):
        p=None
        for i in range(r,len(M)):
            if M[i][c]!=0: p=i; break
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==len(M): break
    return M[:r],piv
def nullspace(M,nc):
    R,piv=rref(M,nc); free=[c for c in range(nc) if c not in piv]; ns=[]
    for f in free:
        v=[Fr(0)]*nc; v[f]=Fr(1)
        for i,c in enumerate(piv): v[c]=-R[i][f]
        ns.append(v)
    return ns
def perm9(b): return F(*rows(b))
hist={}; hard=[]; cex=[]
for V in spans:
    V=[[Fr(int(x)) for x in v] for v in V]
    lin=[DD(V[i],V[j]) for i in range(4) for j in range(i,4)]
    BV=nullspace(lin,9)                      # contains V_0
    # complement of V_0 in B_V
    R,piv=rref(V,9); comp=[]
    cur=[list(r) for r in V]
    for b in BV:
        if len(rref(cur+[b],9)[0])>len(rref(cur,9)[0]): cur.append(b); comp.append(b)
    w=len(comp)
    if w==0: hist[(0,'no base point')]=hist.get((0,'no base point'),0)+1; continue
    Q=[[[D(V[i],comp[a],comp[b]) for b in range(w)] for a in range(w)] for i in range(4)]
    allzero=all(x==0 for q in Q for r in q for x in r)
    # cubic on W: is it identically zero?  evaluate on a grid of y in {0,1,2,3}^w (degree <= 3 in each variable)
    def pval(y): return perm9([sum(y[k]*comp[k][c] for k in range(w)) for c in range(9)])
    if w<=3: pz=all(pval(y)==0 for y in itertools.product(range(4),repeat=w))
    else: pz=None
    if allzero:
        if pz is False: cex.append(V); hist[(w,'COUNTEREXAMPLE: quadrics vanish identically, perm not')]=hist.get((w,'COUNTEREXAMPLE: quadrics vanish identically, perm not'),0)+1
        else: hist[(w,'quadrics = 0 and perm = 0 on W')]=hist.get((w,'quadrics = 0 and perm = 0 on W'),0)+1 if pz else hist.get((w,'quadrics = 0, perm undecided'),0)+1
        continue
    if pz: hist[(w,'perm = 0 on all admissible b')]=hist.get((w,'perm = 0 on all admissible b'),0)+1; continue
    if w==1:
        hist[(1,'quadric != 0 at the only b')]=hist.get((1,'quadric != 0 at the only b'),0)+1; continue
    hard.append((V,comp,Q)); hist[(w,'needs solving')]=hist.get((w,'needs solving'),0)+1
for k,v in sorted(hist.items(),key=str): print(k,v)
print('counterexamples:',len(cex),' cases needing a solve:',len(hard),' time %.0fs'%(time.time()-t0))
pickle.dump(hard,open('/home/kevxhk/work/L-gct-210/verify2/n3p_hard.pkl','wb'))
