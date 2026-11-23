import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""LM search for strongly level spaces of 4x5 matrices (Grassmannian chart), with calibration runs."""
import numpy as np, itertools, time
from core import *
TR = [[c for c in itertools.combinations([a for a in range(5) if a != m], 3)] for m in range(5)]
def res(Y, useP4=True):
    """Y (n,4,5) column-sum-zero. residuals P_2,P_3,(P_4) of the 5 deletions via the column formulas (verified in test2)"""
    out = []
    G = np.einsum('nia,nib->nab', Y, Y); tot = G.sum((1, 2)); tr = np.einsum('naa->n', G)
    for m in range(5):
        sm = tot - 2 * G[:, m, :].sum(1) + G[:, m, m]; out.append(-(sm - (tr - G[:, m, m])) / 2)
        out.append(2 * sum((Y[:, :, a] * Y[:, :, b] * Y[:, :, c]).sum(1) for a, b, c in TR[m]))
        if useP4: out.append(perm(np.delete(Y, m, axis=2)))
    return np.concatenate(out)
def ambient(kind):
    """orthonormal basis (D,4,5) of column-sum-zero ('cs', D=15) or doubly centred ('dc', D=12) 4x5 matrices"""
    E = np.eye(20).reshape(20, 4, 5); E = E - E.mean(1, keepdims=True)
    if kind == 'dc': E = E - E.mean(2, keepdims=True)
    u, s, vh = np.linalg.svd(E.reshape(20, 20)); r = int(np.sum(s > 1e-9)); return vh[:r].reshape(r, 4, 5)
class Prob:
    def __init__(self, k, kind='cs', useP4=True, ns=None, seed=0):
        self.k, self.A, self.useP4 = k, ambient(kind), useP4; self.D = len(self.A)
        rng = np.random.default_rng(seed); self.rng = rng
        ns = ns or (2 * [0, 3, 12, 31, 65][k] // 3 + 12)
        self.c = rng.normal(size=(ns, k)) + 1j * rng.normal(size=(ns, k)); self.c /= np.linalg.norm(self.c, axis=1, keepdims=True)
        q, _ = np.linalg.qr(rng.normal(size=(self.D, self.D)) + 1j * rng.normal(size=(self.D, self.D))); self.U = q
    def basis(self, X):
        Bc = np.concatenate([np.eye(self.k), X.reshape(self.k, self.D - self.k)], 1) @ self.U
        return np.einsum('kd,dab->kab', Bc, self.A)
    def r(self, X):
        return res(np.einsum('nk,kab->nab', self.c, self.basis(X)), self.useP4)
    def solve(self, X0, iters=300, tol=1e-13):
        X = X0.copy(); lam = 1e-2; r = self.r(X); f = np.vdot(r, r).real; h = 1e-7
        for it in range(iters):
            J = np.empty((len(r), len(X)), complex)
            for i in range(len(X)):
                Xp = X.copy(); Xp[i] += h; J[:, i] = (self.r(Xp) - r) / h
            g = J.conj().T @ r; H = J.conj().T @ J
            for _ in range(12):
                d = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g); rn = self.r(X + d); fn = np.vdot(rn, rn).real
                if fn < f: X, r, f, lam = X + d, rn, fn, max(lam / 5, 1e-12); break
                lam *= 5
            else: break
            if f < tol ** 2: break
        return X, np.sqrt(f)
    def chart_of(self, B):
        """chart coordinates X of a given space (B (k,4,5))"""
        C = np.einsum('kab,dab->kd', B, self.A.conj()) @ self.U.conj().T
        return (np.linalg.solve(C[:, :self.k], C[:, self.k:])).ravel()
def qd(B):
    S = B.sum(-1); q = rank(S, 1e-7)
    return q, rank(B, 1e-7) - q
def run(k, kind, useP4, starts, seed, scale=1.0, plant=None, noise=0.0, tmax=150):
    t0 = time.time(); hits = []
    for st in range(starts):
        if time.time() - t0 > tmax: print('   (time cap)'); break
        P = Prob(k, kind, useP4, seed=seed + 1000 * st); n = k * (P.D - k)
        if plant is None: X0 = (P.rng.normal(size=n) + 1j * P.rng.normal(size=n)) * scale
        else:
            Bp = plant + noise * (P.rng.normal(size=plant.shape) + 1j * P.rng.normal(size=plant.shape))
            Bp = Bp - Bp.mean(1, keepdims=True)
            if kind == 'dc': Bp = Bp - Bp.mean(2, keepdims=True)
            X0 = P.chart_of(Bp)
        X, f = P.solve(X0); B = P.basis(X)
        fresh = sl_check(B, trials=100, seed=99) if useP4 else None
        ok = f < 1e-10
        if ok: hits.append(B)
        print(f'   k={k} {kind} P4={useP4} start {st}: resid {f:.1e}' + (f' fresh {fresh:.1e}' if useP4 else '') + (f' (q,d)={qd(B)}' if ok else ''), flush=True)
    print(f'  => {len(hits)}/{st + 1} converged, {time.time() - t0:.0f}s')
    return hits
if __name__ == '__main__':
    mode = sys.argv[1]; args = sys.argv[2:]
    if mode == 'rand':
        k, kind, useP4, starts, seed = int(args[0]), args[1], args[2] == '1', int(args[3]), int(args[4])
        hits = run(k, kind, useP4, starts, seed)
        np.save(f'hits_{k}_{kind}_{int(useP4)}_{seed}.npy', np.array(hits)) if hits else None
