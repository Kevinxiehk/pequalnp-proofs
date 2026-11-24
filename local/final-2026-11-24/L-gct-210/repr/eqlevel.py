import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/repr")
import numpy as np, itertools, math
from equiv import cyc, action, eigdecomp

PERMS = np.array(list(itertools.permutations(range(5))))
SV = np.arange(6.0)
VinvT = np.linalg.inv(np.vander(SV, 6, increasing=True))


def Pall(ts):
    """ts: (N,25) complex -> (N,6) array of P_0..P_5"""
    ts = np.asarray(ts).reshape(-1, 5, 5)
    out = []
    for s in SV:
        A = 1 + s * ts
        out.append(A[:, np.arange(5)[None, :], PERMS].prod(-1).sum(-1))
    vals = np.array(out).T  # N x 6 values of perm(J+s t)
    coef = vals @ VinvT.T  # coefficients of s^k
    fac = np.array([math.factorial(5 - k) for k in range(6)])
    return coef / fac


def polar_nonzero(xs, k):
    # sum over subsets of (-1)^{k-|S|} P_k(sum_S x)
    tot = 0
    pts = []; sg = []
    for r in range(1, k + 1):
        for S in itertools.combinations(range(k), r):
            pts.append(sum(xs[i] for i in S)); sg.append((-1) ** (k - r))
    vals = Pall(np.array(pts))[:, k]
    tot = np.dot(sg, vals)
    return abs(tot) > 1e-7 * (1 + np.abs(vals).max())


CT = np.array([[math.comb(k + mu - 1, mu) if mu else 1 for mu in range(6)] for k in range(30)])


def count_eq(kv, forms):
    keys = sorted(kv)
    F = np.array([[ms.count(a) for a in keys] for ms in forms]) if not isinstance(forms, np.ndarray) else forms
    kvv = np.array([kv[a] for a in keys])
    return int(CT[kvv[None, :], F].prod(1).sum())


def analyse(elem, Ks=(6, 7, 8, 9), kmax=5, rs=np.random.RandomState(0)):
    m, sp = eigdecomp(action(*elem))
    keys = sorted(sp)
    forms = []
    for k in range(2, kmax + 1):
        for ms in itertools.combinations_with_replacement(keys, k):
            if sum(ms) % m:
                continue
            ok = False
            for trial in range(2):
                xs = [sp[a] @ (rs.randn(sp[a].shape[1]) + 1j * rs.randn(sp[a].shape[1])) for a in ms]
                if polar_nonzero(xs, k):
                    ok = True; break
            if ok:
                forms.append(ms)
    dims = {a: sp[a].shape[1] for a in keys}
    formsF = np.array([[ms.count(a) for a in keys] for ms in forms]) if forms else np.zeros((0, len(keys)), int)
    res = {}
    for K in Ks:
        best = None
        ranges = [range(dims[a] + 1) for a in keys]
        nvec = np.prod([dims[a] + 1 for a in keys])
        if nvec < 3e5:
            it = (kv for kv in itertools.product(*ranges) if sum(kv) == K)
        else:
            def gen():
                for _ in range(4000):
                    kv = [0] * len(keys)
                    order = rs.permutation(len(keys))
                    left = K
                    for j in order:
                        take = min(dims[keys[j]], rs.randint(0, left + 1))
                        kv[j] = take; left -= take
                    if left == 0:
                        yield tuple(kv)
            it = gen()
        for kv in it:
            kd = dict(zip(keys, kv))
            unk = sum(kd[a] * (dims[a] - kd[a]) for a in keys)
            e = count_eq(kd, formsF) if len(formsF) else 0
            if best is None or unk - e > best[0]:
                best = (unk - e, {a: kd[a] for a in keys if kd[a]}, unk, e)
        res[K] = best
    return m, dims, forms, res


if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    types = list(cyc)
    seen = set(); out = []
    elems = [(s, tt, 0) for s in types for tt in types] + [(s, 'e', 1) for s in types]
    for (s, tt, tr) in elems:
        if (s, tt, tr) == ('e', 'e', 0):
            continue
        key = tuple(sorted([s, tt])) + (tr,)
        if key in seen:
            continue
        seen.add(key)
        m, dims, forms, res = analyse((s, tt, tr), kmax=kmax)
        out.append(((s, tt, tr), m, dims, res))
        print((s, tt, tr), "m", m, "K6", res[6][:1], "K7", res[7], flush=True)
