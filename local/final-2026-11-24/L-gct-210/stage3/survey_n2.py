import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/stage3")
from s3lib import *
from test_lemmas import spaces, transpose
# survey: in the known level spaces, row pairs (a,b) whose X_ab has "N2 shape": X_ab contains V (x) (sum-zero) on the rows c,d,e,
# i.e. m_cd = m_ce = m_de = 2 with Y_cd + Y_ce 4-dim and no single-row elements in rows c,d,e.
def zdim(B,r):
    return len(XS(B,rows=[i for i in R5 if i!=r]))
for name,B0 in spaces():
    for tr,B in (('',B0),('^T',transpose(B0))):
        a_r=[5-projdim(B,[(r,j) for j in R5]) for r in R5]
        out=[]
        for (a,b) in PAIRS:
            S=[r for r in R5 if r not in (a,b)]
            lam=len(XS(B,rows=[a,b])); la=len(XS(B,rows=[a])); lb=len(XS(B,rows=[b]))
            m=[len(XS(B,rows=[a,b,i])) for i in S]            # 2-row elements on the two rows of S other than i
            z=[zdim(B,i) for i in S]
            pd=[projdim(XS(B,rows=[a,b]),[(i,j) for j in R5]) if lam>0 else 0 for i in S]
            if min(m)>=2 and max(z)==0:
                out.append(((a,b),'lam',lam,'dimL_a,L_b',la,lb,'m',m,'z',z,'rowdims of X_ab',pd))
        print(name+tr,'dim',len(B),'a_r',a_r,'N2-shaped pairs:',len(out))
        for o in out: print('    ',*o)
