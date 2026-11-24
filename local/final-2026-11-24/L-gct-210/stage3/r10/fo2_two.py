import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2'); import fo2lib
for f in ['/home/kevxhk/work/L-gct-210/rows/clm_p4_d5_defect2_s9.npy','/home/kevxhk/work/L-gct-210/rows/ncdef_d5_e2_k1_s1.npy','/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_7_13.npy']:
    Z=np.load(f); B=np.zeros((len(Z),5,5),complex); B[:,1:,:]=Z
    for seed in (1,2):
        r=fo2lib.fo2(B,np.random.default_rng(seed),npts=120,nq=6)
        print(f.split('/')[-1],'seed',seed,': dim T_1 %d, rank of random q-combination on T_1 %d, FO2 bound %d  (N in T_1: %.0e, N isotropic: %.0e)'%r[:5])
