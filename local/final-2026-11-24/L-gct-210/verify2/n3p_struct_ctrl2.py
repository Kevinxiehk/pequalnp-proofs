# verify2: control for the "perm = 0 on a complement of V_0 in B_V" criterion: same code path for 3-dim spans (cells only + cell pairs),
# where valid base points exist. Expect many spans with perm NOT identically 0 on the complement.
import itertools, random, numpy as np
from fractions import Fraction as Fr
src=open('/home/kevxhk/work/L-gct-210/verify2/n3p_struct2.py').read()
head=src.split("hist={}; hard=[]; cex=[]")[0].replace("spans=pickle.load(open('/home/kevxhk/work/L-gct-210/verify2/n3p_spans.pkl','rb'))","spans=[]")
exec(head)
cells=[(i,j) for i in range(3) for j in range(3)]
els=[]
for c in range(9):
    v=[0]*9; v[c]=1; els.append(v)
for a in range(9):
    for b in range(a+1,9):
        if cells[a][0]==cells[b][0] or cells[a][1]==cells[b][1]:
            for sg in (1,-1):
                v=[0]*9; v[a]=1; v[b]=sg; els.append(v)
random.seed(4); hist={}; seen=set(); valid=0
subs=list(itertools.combinations(range(len(els)),3)); random.shuffle(subs)
for sub in subs[:2500]:
    V=[[Fr(x) for x in els[i]] for i in sub]
    R,piv=rref(V,9)
    if len(R)<3: continue
    key=tuple(tuple(r) for r in R)
    if key in seen: continue
    seen.add(key)
    if any(perm9([sum(y[i]*V[i][c] for i in range(3)) for c in range(9)])!=0 for y in itertools.product(range(4),repeat=3)): continue
    lin=[DD(V[i],V[j]) for i in range(3) for j in range(i,3)]
    BV=nullspace(lin,9); cur=[list(r) for r in V]; comp=[]
    for b in BV:
        if len(rref(cur+[b],9)[0])>len(rref(cur,9)[0]): cur.append(b); comp.append(b)
    w=len(comp)
    pts=[[Fr(random.randint(-3,3)) for _ in range(w)] for _ in range(40)]
    pz=all(perm9([sum(y[k]*comp[k][c] for k in range(w)) for c in range(9)])==0 for y in pts)
    # is there a valid base point among small integer points of the complement?  (quadrics = 0 and perm != 0)
    found=False
    if not pz:
        for y in pts+[[Fr(int(k==a)) for k in range(w)] for a in range(w)]+[[Fr(1)]*w]:
            b=[sum(y[k]*comp[k][c] for k in range(w)) for c in range(9)]
            if perm9(b)!=0 and all(D(V[i],b,b)==0 for i in range(3)): found=True; break
    k=(w,'perm = 0 on complement' if pz else ('perm != 0 on complement'+(', valid base point found' if found else '')))
    hist[k]=hist.get(k,0)+1; valid+=found
for k,v in sorted(hist.items(),key=str): print(k,v)
print('3-dim spans inside {perm=0} examined:',sum(hist.values()),' with an explicit valid base point (perm != 0):',valid)
