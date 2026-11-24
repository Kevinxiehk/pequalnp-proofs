import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2/r24')
exec(open('/home/kevxhk/work/L-gct-210/verify2/r24/f2col_cut.py').read())
import itertools
# strata with a1 != 0 for R2 (S_3 on positions 2,3,4 = indices 1,2,3); special Z = zero set {2,3,4} excluded (row 15)
def strata_a1nz():
    out=[]
    for r in range(0,3):
        for Zs in itertools.combinations((1,2,3),r): out.append(Zs)
    return out
X_R2=[H,A,D]+P01
run('R2 generic nu: X = H u A u D u {0,1}^3',X_R2,S3,strata_a1nz())
run('R2 nu = 0 slice: X = H u A u D u J0 u {0,1}^3',X_R2+[J],S3,strata_a1nz())
X_R1=[H,A,D,pt((1,1,1,1))]
run('R1 generic lam: X = H u A u D u {(1,1,1)} (char-p RD)',X_R1,S3,strata_a1nz())
# cross-type: S_4 on all four positions; strata with all nonzero, then boundary a1 = 0 handled as the A-type family below
run('cross-type lam=0: X = H u A u D u J u {0,1}^3, S_4, region all nonzero',X_R2+[J],S4,[()])
