exec(open('/home/kevxhk/work/L-gct-210/verify2/r24/f2col_cut.py').read())
import itertools
def strata_in_A():   # index 0 (a1) always zero; zero subsets of {a2,a3,a4} of size <= 1 (size 2 = points handled by the sub-family, size 3 = special Z)
    return [(0,)+Zs for r in range(0,2) for Zs in itertools.combinations((1,2,3),r)]
HA=hyp((0,1,2,-6)); A2=hyp((0,1,0,0)); DA=hyp((0,1,1,-4)); JA=hyp((0,1,1,1))
RDA=[pt((0,1,0,1)),pt((0,1,1,1)),pt((0,0,1,1)),pt((0,0,0,1))]
run('R2 A family (a1=0) [also cross-type boundary a1=0]: X = H_A u {a2=0} u D_A u J_A u RD_A',[HA,A2,DA,JA]+RDA,S3,strata_in_A())
run('R2 J_A family: X = {a3 = 7a4} u {a3 + a4 = 0}',[hyp((0,0,1,-7)),hyp((0,0,1,1))],S3,[(0,)+Zs for r in range(0,2) for Zs in itertools.combinations((1,2,3),r)],extra=[[0,1,1,1]])
run('R2 nu=0 J0 family: X = {a2+a3 = 7a4} u A',[hyp((0,1,1,-7)),A],S3,[Zs for r in range(0,2) for Zs in itertools.combinations((1,2,3),r)],extra=[[1,1,1,1]])
