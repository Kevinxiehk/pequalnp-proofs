import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""more (4,1) spaces with fixed non-two-column m: are they all split?"""
import numpy as np
from core import *
from di_core import *
from di_gr import gr_search
from r3_gr import describe
ms = {'(1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.]), '(1,2,-4,1,0)': np.array([1, 2, -4, 1, 0.]), '(1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.])}
tot = 0; nonsplit = 0
for nm, m in ms.items():
    hits, n, t = gr_search(4, m, 60, 900 + len(nm), 110)
    print('m = %s: Gr(4,17): %d/%d converged (%.0fs)' % (nm, len(hits), n, t), flush=True)
    for B in hits:
        d = describe(B, m); tot += 1; nonsplit += ('split rows []' in d); print('    ', d, flush=True)
    if hits: np.save('r3_gr2_%d.npy' % len(nm), np.array(hits))
print('total (4,1) hits %d, non-split %d' % (tot, nonsplit))
