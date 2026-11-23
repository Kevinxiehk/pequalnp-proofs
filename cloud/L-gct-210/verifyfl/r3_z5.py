import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""do the column-centred (3,1) spaces with good m (kappa == 0, NOT strongly level) extend to dimension 4?
   (an extension would be a NON-split (4,1) space with good m, i.e. a counterexample to (NS4')/(K4))."""
import numpy as np, time
from core import *
from di_core import *
from r3_z import search
from di_ext import ext, chk_m
m = np.array([1, 2, -3, 0, 0.]); t0 = time.time()
hits, n, t = search(3, m, 40, 2024, 45)
gen = [B for B in hits if sl_check(B, trials=30) > 1e-5]
print('m = (1,2,-3,0,0): %d/%d column-centred 3-dim hits, %d with genuine defect (%.0fs)' % (len(hits), n, len(gen), t), flush=True)
if gen: np.save('r3_z3_good.npy', np.array(gen))
tot = 0; tried = 0
for i, B in enumerate(gen[:6]):
    if time.time() - t0 > 105: break
    s, k = ext(B, m, 14, 300 + i, tmax=11); tot += len(s); tried += k
    print('   space %d: defect residual %.0e, q = %d; extensions to dim 4: %d/%d' % (i, chk_m(B, m), rank(B.sum(-1), 1e-7), len(s), k), flush=True)
    if s: np.save('r3_nonsplit4_%d.npy' % i, np.concatenate([B, s[0][None]]))
print('total extensions %d of %d starts' % (tot, tried))
