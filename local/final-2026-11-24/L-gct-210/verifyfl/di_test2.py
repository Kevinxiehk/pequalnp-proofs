import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""structure of the e = 1 examples: kappa (column-sum form), L'_0 = ker kappa, is L'_0 strongly level?, theta rank, q, d."""
import numpy as np
from core import *
from di_core import *
sp = load_rows('clm_p4_d4_defect1_s*.npy'); sp.update(load_rows('seed_d4_e1_t*.npy'))
sp['cand_M2'] = onb(np.load('/home/kevxhk/work/L-gct-210/rows/cand_M2.npy'))
rng = np.random.default_rng(0)
for nm, B in sp.items():
    e, Cb, lev, sv = defect(B)
    if e != 1: print(nm, 'e =', e); continue
    m = Cb[0]; m = m / m[np.argmax(np.abs(m))]
    cs = B.sum(1)                                        # (d,5) column sums
    kap_rank = rank(cs, 1e-8)
    L0, r = kernel_of(B, lambda Y: Y.sum(0))
    sl0 = sl_check(L0, trials=60) if len(L0) else 0
    S0 = L0.sum(-1) if len(L0) else np.zeros((0, 4)); q0 = rank(S0, 1e-7) if len(L0) else 0
    N0, _ = kernel_of(L0, lambda Y: Y.sum(1)) if len(L0) else (np.zeros((0, 4, 5)), 0)
    # single-row elements e_i m^T ?
    split = []
    for i in range(4):
        E = np.zeros((4, 5), complex); E[i] = m
        if rank(np.concatenate([B, E[None]]).reshape(len(B) + 1, -1), 1e-7) == len(B): split.append(i)
    print(f'{nm:28s} d={len(B)} #zeros(m)={int(np.sum(np.abs(m) < 1e-6))} kappa rank {kap_rank} dim L0={len(L0)} strong-level err of L0 {sl0:.1e} (q0,d0)=({q0},{len(N0)}) split rows {split}')
