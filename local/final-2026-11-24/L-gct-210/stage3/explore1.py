import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/stage3")
from s3lib import *
rng=np.random.default_rng(3)
for name,f in SP.items():
    B=f(); print('=====',name,len(B))
    a=[5-projdim(B,[(r,j) for j in R5]) for r in R5]; b=[5-projdim(B,[(i,c) for i in R5]) for c in R5]
    print(' a_r',a,' b_c',b)
    print(' lam rows', {p:len(XS(B,rows=p)) for p in PAIRS})
    print(' lam cols', {p:len(XS(B,cols=p)) for p in PAIRS})
    print(' m_ab (2-row elems)', {p:len(XS(B,rows=[r for r in R5 if r not in p])) for p in PAIRS})
    print(' m^ab (2-col elems)', {p:len(XS(B,cols=[r for r in R5 if r not in p])) for p in PAIRS})
    print(' z_r (single row)', [len(XS(B,rows=[r for r in R5 if r!=a_])) for a_ in R5], ' z^c', [len(XS(B,cols=[r for r in R5 if r!=a_])) for a_ in R5])
    # ell-supporting 3x2 blocks and 2x3, 4x1, 1x4, 2x2,...
    for (p,q) in [(3,2),(2,3),(4,1),(1,4),(2,2),(3,1),(1,3),(1,2),(2,1),(1,1)]:
        cnt=0; tot=0; lst=[]
        for S in itertools.combinations(R5,p):
            for T in itertools.combinations(R5,q):
                tot+=1
                if ell_supporting(B,[(i,j) for i in S for j in T]): cnt+=1; lst.append((S,T))
        print('  ell-supporting %dx%d blocks: %d of %d'%(p,q,cnt,tot), lst[:6] if cnt<=6 else '')
