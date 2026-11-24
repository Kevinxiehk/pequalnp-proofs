import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""(SL_m): column-centred 4-dim spaces with defect inside C m.  LM on Gr(4,15); two-column m is the positive control."""
import numpy as np
from core import *
from r3_z import search
w = w3; z5 = np.exp(2j * np.pi / 5)
ms = {'two-column (control)': np.array([1, -1, 0, 0, 0.]),
      'isotropic (1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0]),
      'isotropic (1,i,-1,-i,0)': np.array([1, 1j, -1, -1j, 0]),
      'isotropic 5th roots': z5 ** np.arange(5),
      'good, full support (1,2,3,-1,-5)': np.array([1, 2, 3, -1, -5.])}
sel = sys.argv[1].split(','); tmax = float(sys.argv[2]); seed = int(sys.argv[3])
for i, (nm, m) in enumerate(ms.items()):
    if str(i) not in sel: continue
    hits, n, t = search(4, m, 60, seed, tmax)
    sl = [sl_check(B, trials=30) for B in hits]
    print('k=4 column-centred, m %-32s: %d/%d converged (%.0fs); strongly level: %d, genuinely defect 1: %d' % (nm, len(hits), n, t, sum(x < 1e-7 for x in sl), sum(x > 1e-5 for x in sl)), flush=True)
