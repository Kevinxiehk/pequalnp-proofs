exec(open('/home/kevxhk/work/L-gct-210/verify2/r24/f2col_cut.py').read())
import itertools
run('R2 J_A family, two zeros among a2..a4',[hyp((0,0,1,-7)),hyp((0,1,0,0))],S3,[(0,)+Zs for Zs in itertools.combinations((1,2,3),2)],extra=[[0,1,1,1]])
run('R2 nu=0 J0 family, two zeros among a2..a4',[hyp((0,1,1,-7)),A],S3,[Zs for Zs in itertools.combinations((1,2,3),2)],extra=[[1,1,1,1]])
run('cross-type, S_4: boundary handled via a1=0 (A-family run); check strata with exactly one zero under S_4 directly',[H,A,D,J]+P01,S4,[(0,),(1,),(2,),(3,)])
