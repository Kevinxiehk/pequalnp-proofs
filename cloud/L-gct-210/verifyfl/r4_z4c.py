import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
import numpy as np
from core import *
from r3_z import search
for nm, m in {'good (1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), 'two-column (control)': np.array([1, -1, 0, 0, 0.])}.items():
    hits, n, t = search(4, m, 200, 4242, 70)
    sl = [sl_check(B, trials=30) for B in hits]
    print('k=4 column-centred, m %-22s: %d/%d converged (%.0fs); strongly level: %d, genuinely defect 1: %d' % (nm, len(hits), n, t, sum(x < 1e-7 for x in sl), sum(x > 1e-5 for x in sl)), flush=True)
