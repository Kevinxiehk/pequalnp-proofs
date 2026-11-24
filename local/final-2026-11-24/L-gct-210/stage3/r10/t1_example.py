# Round 10: for a 5-dim 4x5 level space N (rows a..d) of shape single-row dims (2,1,0,0) / row projections (2,2,2,2) -- the shape of L_r in the
# mixed pattern z = (2,1,..) -- compute dim T_1 of N embedded as a 5x5 space with the remaining row zero (each of the 5 positions of the
# zero row): a 9-dim level L containing N as L_r must lie in T_1(N), so dim T_1 <= 8 rules this N out in that role.
import sys, glob, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); from t1_c52 import T1, single_rows, rank
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_*.npy')+glob.glob('/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_*.npy')):
    Z=np.load(f); d=len(Z)
    print(f.split('/')[-1],'single-row dims',single_rows(Z),'row-proj',[rank(Z[:,r,:]) for r in range(4)])
    for pos in range(5):
        B=np.zeros((d,5,5),complex); rows=[i for i in range(5) if i!=pos]; B[:,rows,:]=Z
        t=T1(B); print('   zero row at position %d: dim T_1 = %d (gap %.0e / %.0e)'%(pos,t[0],t[1],t[2]))
