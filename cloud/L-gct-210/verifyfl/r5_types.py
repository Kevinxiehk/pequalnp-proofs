import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Round 5: landscape of column-centred spaces with defect in C m (|supp m| = 3): types (q,d), the DC part N, activity of the neutral columns."""
import numpy as np, time
from core import *
from di_core import *
from r3_z import search
dot = lambda a, b: np.sum(a * b)
def describe(B, m):
    B = onb(B); k = len(B); P = [j for j in range(5) if abs(m[j]) > 1e-9]; Nt = [j for j in range(5) if j not in P]
    q = rank(B.sum(-1), 1e-6); N, _ = kernel_of(B, lambda Y: Y.sum(1)); d = len(N)
    sl = sl_check(B, trials=20)
    neut = [rank(B[:, :, j], 1e-6) for j in Nt]
    out = 'dim %d (q,d) = (%d,%d) %s; ranks of neutral columns %s' % (k, q, d, 'STRONGLY LEVEL' if sl < 1e-7 else 'defect', neut)
    if d >= 1:
        for Z in N[:2]:
            th = [dot(Z[:, j], Z[:, j]) / m[j] for j in P]; out += '; Z_*: vartheta %.2e, col ranks %s, rank Z %d, neutral norms %s' % (
                abs(th[0]), [int(np.linalg.norm(Z[:, j]) > 1e-6) for j in range(5)], rank(Z, 1e-6), np.round([np.linalg.norm(Z[:, j]) for j in Nt], 3))
    return out
if __name__ == '__main__':
    k = int(sys.argv[1]); tmax = float(sys.argv[2]); seed = int(sys.argv[3])
    w = w3; ms = {'good (1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), 'iso (1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0])}
    for nm, m in ms.items():
        if len(sys.argv) > 4 and sys.argv[4] not in nm: continue
        hits, n, t = search(k, m, 400, seed, tmax)
        print('%s, k = %d: %d/%d converged (%.0fs)' % (nm, k, len(hits), n, t), flush=True)
        seen = {}
        for B in hits:
            dsc = describe(B, m); key = dsc.split(';')[0] + ';' + dsc.split(';')[1]
            seen[key] = seen.get(key, 0) + 1
            if seen[key] <= 2: print('   ', dsc, flush=True)
        for kx, v in seen.items(): print('  count %3d : %s' % (v, kx))
        np.save('r5_types_k%d_%s.npy' % (k, nm[:4].strip()), np.array(hits))
