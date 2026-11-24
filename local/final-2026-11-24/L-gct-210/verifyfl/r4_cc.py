import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
import numpy as np, glob
from core import *
from di_core import *
sp = {}; out = {}
for f_ in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/*.npy')):
    try:
        A = np.load(f_)
        if A.ndim == 3 and A.shape[1:] == (4, 5): sp['rows:' + f_.split('/')[-1]] = A
    except Exception: pass
for f_ in sorted(glob.glob('*.npy')):
    try:
        A = np.load(f_)
        if A.ndim == 3 and A.shape[1:] == (4, 5): sp['mine:' + f_] = A
        elif A.ndim == 4 and A.shape[2:] == (4, 5):
            for i, B in enumerate(A): sp['mine:%s#%d' % (f_, i)] = B
    except Exception: pass
for nm, B in sp.items():
    try:
        B = np.asarray(B, complex)
        if B.ndim != 3 or B.shape[1:] != (4, 5) or len(B) != 4: continue
        B = onb(B); e, Cb, lev, sv = defect(B)
        if e != 1 or lev > 1e-8: continue
        m = Cb[0]; m = m / m[np.argmax(np.abs(m))]; two = int(np.sum(np.abs(m) > 1e-6)) == 2
        kr = rank(np.array([b.sum(0) for b in B]), 1e-7)
        if kr == 0: print('column-centred (4,1): %-40s two-column: %s  m = %s' % (nm, two, np.round(m, 3)))
        out[(two, kr)] = out.get((two, kr), 0) + 1
    except Exception as ex: pass
print('(two-column, kappa-rank) -> count over all 4-dim e = 1 spaces on file:', out)
