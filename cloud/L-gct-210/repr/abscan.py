import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/repr")
import numpy as np, itertools, math
from eqlevel import Pall, polar_nonzero, CT
from equiv import permmat, Wb

SUB = {'1': [], 'Z2': [[(0, 1)]], 'Z2b': [[(0, 1), (2, 3)]], 'Z3': [[(0, 1, 2)]], 'Z4': [[(0, 1, 2, 3)]],
       'Z5': [[(0, 1, 2, 3, 4)]], 'Z6': [[(0, 1, 2), (3, 4)]], 'K4a': [[(0, 1)], [(2, 3)]],
       'K4b': [[(0, 1), (2, 3)], [(0, 2), (1, 3)]], 'Z3Z2': [[(0, 1, 2)], [(3, 4)]]}


def mat_action(Ps, Pt, transp=False):
    cols = []
    for k in range(25):
        X = np.zeros(25); X[k] = 1; X = X.reshape(5, 5)
        Y = Ps @ X @ Pt.T
        if transp: Y = Y.T
        cols.append(Y.ravel())
    return Wb.T @ np.array(cols).T @ Wb


def joint_eig(gens):
    spaces = {(): np.eye(24, dtype=complex)}
    orders = []
    for A in gens:
        m = 1
        while not np.allclose(np.linalg.matrix_power(A, m), np.eye(24)): m += 1
        orders.append(m)
        pw = [np.linalg.matrix_power(A, j) for j in range(m)]
        new = {}
        for key, S in spaces.items():
            for k in range(m):
                z = np.exp(2j * np.pi * k / m)
                P = sum(z ** (-j) * pw[j] for j in range(m)) / m
                M = P @ S
                if np.linalg.norm(M) < 1e-9: continue
                U, s, _ = np.linalg.svd(M, full_matrices=False)
                r = np.sum(s > 1e-8)
                if r: new[key + (k,)] = U[:, :r]
        spaces = new
    return orders, {k: Wb @ v for k, v in spaces.items()}


def analyse(gens, Ks=(7, 8, 9), rs=np.random.RandomState(0)):
    orders, sp = joint_eig(gens)
    keys = sorted(sp)
    forms = []
    for k in range(2, 6):
        for ms in itertools.combinations_with_replacement(range(len(keys)), k):
            if any(sum(keys[a][c] for a in ms) % orders[c] for c in range(len(orders))): continue
            ok = False
            for trial in range(2):
                xs = [sp[keys[a]] @ (rs.randn(sp[keys[a]].shape[1]) + 1j * rs.randn(sp[keys[a]].shape[1])) for a in ms]
                if polar_nonzero(xs, k): ok = True; break
            if ok: forms.append(ms)
    dims = np.array([sp[k].shape[1] for k in keys])
    F = np.array([[ms.count(a) for a in range(len(keys))] for ms in forms]) if forms else np.zeros((0, len(keys)), int)

    def ex(kv):
        unk = int((kv * (dims - kv)).sum())
        e = int(CT[kv[None, :], F].prod(1).sum()) if len(F) else 0
        return unk - e, unk, e
    res = {}
    for K in Ks:
        best = (-10 ** 9,)
        for rep in range(150):
            kv = np.zeros(len(keys), int); left = K
            for j in rs.permutation(len(keys)):
                t = min(dims[j], rs.randint(0, left + 1)); kv[j] = t; left -= t
            if left: continue
            cur = ex(kv)
            improved = True
            while improved:
                improved = False
                for a in range(len(keys)):
                    if kv[a] == 0: continue
                    for b in range(len(keys)):
                        if b == a or kv[b] >= dims[b]: continue
                        kv[a] -= 1; kv[b] += 1
                        c = ex(kv)
                        if c[0] > cur[0]: cur = c; improved = True
                        else: kv[a] += 1; kv[b] -= 1
            if cur[0] > best[0]: best = (cur[0], {keys[a]: int(kv[a]) for a in range(len(keys)) if kv[a]}, cur[1], cur[2])
        res[K] = best
    return orders, dict(zip(keys, dims)), res


if __name__ == '__main__':
    names = list(SUB)
    I5 = np.eye(5)
    done = set()
    for a in names:
        for b in names:
            if (b, a) in done or (a, b) == ('1', '1'): continue
            done.add((a, b))
            gens = [mat_action(permmat(g), I5) for g in SUB[a]] + [mat_action(I5, permmat(g)) for g in SUB[b]]
            if len(gens) < 2: continue  # cyclic cases already scanned
            orders, dims, res = analyse(gens)
            print(a, b, orders, 'K7', res[7][:1], 'K8', res[8], 'K9', res[9][:1], flush=True)
