import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""census of rows' e = 1 examples; Lemma EQ (equal columns => strongly level) on all of them."""
import numpy as np
from core import *
from di_core import *
sp = load_rows('clm_p4_d4_defect1_s*.npy')
for f in ('cand_M2.npy',):
    try: sp[f] = onb(np.load('/home/claude/work/L-gct-210/rows/' + f))
    except Exception as ex: print('skip', f, ex)
for nm, B in sp.items():
    e, Cb, lev, sv = defect(B)
    m = Cb[0] / np.abs(Cb[0]).max() if e else None
    msg = f'{nm:28s} dim {len(B)} e={e} level err {lev:.1e}'
    if e == 1:
        j0 = np.argmax(np.abs(m)); m = m / m[j0]
        msg += ' m = ' + np.array2string(np.round(m, 3), precision=3, suppress_small=True)
        # Lemma EQ: for a != b with m_a != m_b the subspace {y_a = y_b} is strongly level
        worst = 0; dims = []
        for a in range(5):
            for b in range(a + 1, 5):
                if abs(m[a] - m[b]) < 1e-6: continue
                K, r = kernel_of(B, lambda Y: Y[:, a] - Y[:, b])
                if len(K): worst = max(worst, sl_check(K, trials=40))
                dims.append(len(K))
        msg += f' | EQ: dims of {{y_a=y_b}} {dims}, max strong-level err {worst:.1e}'
    print(msg)
