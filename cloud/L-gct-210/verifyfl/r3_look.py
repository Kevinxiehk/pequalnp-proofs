import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""structure of the split (4,1) examples: split row i, m, L'_0 = ker kappa: column ranks, row ranks, supports."""
import numpy as np
from core import *
from di_core import *
sp = load_rows('clm_p4_d4_defect1_s*.npy'); sp.update(load_rows('seed_d4_e1_t*.npy'))
np.set_printoptions(linewidth=200, precision=3, suppress=True)
for nm, B in sp.items():
    e, Cb, lev, sv = defect(B)
    if e != 1: continue
    m = Cb[0]; m = m / m[np.argmax(np.abs(m))]
    split = []
    for i in range(4):
        E = np.zeros((4, 5), complex); E[i] = m
        if rank(np.concatenate([B, E[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B): split.append(i)
    if not split: print(nm, 'not split'); continue
    i = split[0]
    L0, r = kernel_of(B, lambda Y: Y.sum(0))
    colrk = [rank(L0[:, :, j], 1e-6) for j in range(5)]; rowrk = [rank(L0[:, k, :], 1e-6) for k in range(4)]
    # row i of L0: constant on supp(m)?
    P = [j for j in range(5) if abs(m[j]) > 1e-6]
    dev = max(np.abs(Y[i, P] - Y[i, P].mean()).max() for Y in L0)
    # 3-row part: rows != i ; ranks of columns restricted to rows != i
    R3 = np.delete(L0, i, axis=1); colrk3 = [rank(R3[:, :, j], 1e-6) for j in range(5)]
    rowi = rank(L0[:, i, :], 1e-6)
    print(f'{nm:26s} split row {i} supp(m)={P} | L0 col ranks {colrk} (rows!=i: {colrk3}) row ranks {rowrk} | row i of L0: rank {rowi}, dev from const on supp(m) {dev:.1e}')
