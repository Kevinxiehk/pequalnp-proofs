import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
from s3lib import *
from test_lemmas import spaces
# is Y_ab spanned by its "Q=0" elements: single-row (rows a or b), dominoes (one column), 2x2-block elements?
def sparse_parts(B,ab):
    S=[r for r in R5 if r not in ab]; a,b=ab
    Y=XS(B,rows=S); m=len(Y)
    if m==0: return None
    parts=[]
    Za=XS(B,rows=S+[b]); Zb=XS(B,rows=S+[a])
    dom=[XS(B,rows=S,cols=[c for c in R5 if c!=j]) for j in R5]
    blk={T:XS(B,rows=S,cols=[c for c in R5 if c not in T]) for T in PAIRS}
    allv=[v.reshape(-1) for A in [Za,Zb]+dom for v in A]
    r_rd=rank(np.array(allv)) if allv else 0
    allv2=allv+[v.reshape(-1) for T in PAIRS for v in blk[T]]
    r_all=rank(np.array(allv2)) if allv2 else 0
    return m,len(Za),len(Zb),sum(len(d) for d in dom),r_rd,r_all
for name,B in spaces():
    out=[]
    for ab in PAIRS:
        r=sparse_parts(B,ab)
        if r: out.append((ab,)+r)
    print(name); 
    for o in out: print('   pair %s: m=%d z_a=%d z_b=%d #dominoes=%d  span(single-row+domino)=%d  span(+2x2 block elems)=%d %s'%(o+(('' if o[6]==o[1] else '  <-- NOT spanned by 2-column-supported elements'),)))
