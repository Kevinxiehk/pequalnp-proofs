import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
for f in A_[1:]:
    B=np.load(f); n,err=T2test(B,np.random.default_rng(1))
    print(f.split('/')[-1],'dim of (T2) solution space (T in C^{5x4x5}) =',n,' (X-ambiguity contributes 5*5=25 if X is 5-dim); J\' distance',err)
