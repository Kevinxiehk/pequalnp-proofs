import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""dim N <= 2: DC one-vector extensions of the two existing types of DC planes (and of LM-found planes)."""
import numpy as np
from core import *
from ext import ext_search, e, zeta, zb
NII = np.array([np.outer(zeta, e[0] - e[1]), np.outer(zb, e[2] - e[3])])
NI = np.array([np.outer(chi(1), e[0] - e[1]), np.outer(chi(1), e[1] - e[2])])
for nm, F in (('type I', NI), ('type II', NII)):
    full, n1 = ext_search(F, 14, 11, kind='dc', tmax=40)
    rel, n2 = ext_search(F, 8, 12, kind='dc', useP4=False, tmax=30)
    print(f'{nm}: DC extensions, full system {len(full)}/{n1}; relaxed (P_2,P_3 only) {len(rel)}/{n2}')
    for Y in rel[:3]:
        # describe relaxed solutions: column ranks and lines
        print('     relaxed solution: active columns', [m for m in range(5) if np.linalg.norm(Y[:, m]) > 1e-6],
              ' |<col,chi_3>| per column', np.round([abs(np.sum(Y[:, m] * chi(3))) for m in range(5)], 3))
