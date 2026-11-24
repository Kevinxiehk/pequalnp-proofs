import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""(I2): isotropic split => row i of every element is orthogonal to m; and c'_j (column sums of the other rows) constant on supp m."""
import numpy as np, glob
from core import *
from di_core import *
for f_ in ['r3_iso_counterexample.npy', 'r3_iso4_s0.npy'] + sorted(glob.glob('r3_iso*.npy')):
    try: A = np.load(f_)
    except Exception as ex: print(f_, ex); continue
    Bs = [A] if A.ndim == 3 else list(A)
    for B in Bs:
        B = onb(B); e, Cb, lev, sv = defect(B)
        if e != 1: print('%-28s dim %d defect %d lev %.1e (skipped)' % (f_, len(B), e, lev)); continue
        m = Cb[0]; m = m / m[np.argmax(np.abs(m))]
        iso = abs(np.sum(m * m)); split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B)]
        out = '%-28s dim %d lev %.1e <m,m> %.1e split rows %s' % (f_, len(B), lev, iso, split)
        for i in split:
            r1 = np.abs(B[:, i, :] @ m).max()
            cp = B.sum(1) - B[:, i, :]; P = np.abs(m) > 1e-6
            r2 = np.abs(cp[:, P] - cp[:, P].mean(1, keepdims=True)).max()
            out += ' | row %d: max|<m,y^i>| %.1e, c\'_j const on P: %.1e' % (i, r1, r2)
        print(out)
