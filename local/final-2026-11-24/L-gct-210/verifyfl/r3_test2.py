import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""e = 2, 3 examples of rows: defect space C, single-row parts U_i (dims), Gram rank of <,> on C, column-sum map gamma,
   is ker gamma strongly level?"""
import numpy as np
from core import *
from di_core import *
sp = load_rows('clm_p4_d5_defect2_s*.npy'); sp.update(load_rows('clm_p4_d6_defect3_s*.npy')); sp.update(load_rows('seed_d5_e2_t*.npy')); sp.update(load_rows('seed_d6_e3_t*.npy'))
np.set_printoptions(linewidth=220, precision=3, suppress=True)
for nm, B in sp.items():
    e, Cb, lev, sv = defect(B)
    if lev > 1e-8: print(nm, 'not level', lev); continue
    Cb = Cb[:e]
    G = Cb @ Cb.T; grk = rank(G, 1e-7) if e else 0                          # bilinear Gram matrix of <,> on C
    U = []
    for i in range(4):
        # single-row part: elements of L' supported on row i
        K, r = kernel_of(B, lambda Y: np.delete(Y, i, axis=0)); U.append(len(K))
    gam = B.sum(1); rg = rank(gam, 1e-7)
    L0, _ = kernel_of(B, lambda Y: Y.sum(0)); sl0 = sl_check(L0, trials=40) if len(L0) else 0
    print(f'{nm:28s} dim {len(B)} e={e} rank<,>|C={grk} single-row dims {U} rank gamma={rg} dim ker gamma={len(L0)} strong-level err {sl0:.1e}')
