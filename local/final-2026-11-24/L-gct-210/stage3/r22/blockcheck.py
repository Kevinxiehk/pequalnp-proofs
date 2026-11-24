# check the BLOCK structure of a special member W (4 x 5): exists B3 (3 columns) such that every row is either supported on B3 with zero sum
# there ('Z'), or constant on B3 ('C').
import numpy as np, itertools, glob, sys
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r22/spec_*.npy')):
    W=np.load(f); best=None
    for B3 in itertools.combinations(range(5),3):
        B2=[j for j in range(5) if j not in B3]; types=[]
        for wv in W:
            sc=np.abs(wv).max()
            z=(np.abs(wv[B2]).max()<1e-7*sc) and abs(wv[list(B3)].sum())<1e-7*sc
            c=np.ptp(wv[list(B3)].real)+np.ptp(wv[list(B3)].imag)<1e-7*sc
            types.append('Z' if z else ('C' if c else '-'))
        if '-' not in types: best=(B3,types); break
    print(f.split('/')[-1],'block structure:',best)
