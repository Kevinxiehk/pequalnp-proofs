import sys, math
sys.path.insert(0, '/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from level import Pk, Pk_grad, construction_2n3
n = 5
w3 = np.exp(2j*np.pi/3)

def E(i, j):
    M = np.zeros((5, 5), complex); M[i, j] = 1; return M

def L080():
    B = []
    for j in range(3): B.append(E(0, j+1)-E(0, 4))
    for i in range(4): B.append(E(i+1, 0)-E(0, 0))
    return np.array(B)

def ex1():
    B = []
    M = np.zeros((5, 5), complex)
    for i in range(3): M[i, 0] = w3**i; M[i, 1] = -w3**i
    B.append(M)
    M = np.zeros((5, 5), complex)
    for i in range(3): M[i, 2] = w3**(2*i); M[i, 3] = -w3**(2*i)
    B.append(M)
    for j in range(4): B.append(E(3, j)-E(3, 4))
    M = np.zeros((5, 5), complex); M[0:3, 4] = 1; M[4, 4] = -3; B.append(M)
    return np.array(B)

def ex2():
    v = np.array([1, w3, w3**2, 0, 0])
    B = []
    for c in (0, 1):
        M = np.zeros((5, 5), complex); M[:, c] = v; B.append(M)
    for j in range(4): B.append(E(3, j)-E(3, 4))
    M = np.zeros((5, 5), complex); M[0:3, 4] = 1; M[4, 4] = -3; B.append(M)
    return np.array(B)

def rc45():
    B = list(ex1()[:6]); return np.array(B)

def W5():
    pass
    from tangent import weight_space
    return np.array(weight_space(5, [1, 2, 3, 4, 0], [1, 2, 0, 4, 3], 30, [2, 3, 4]), complex)

def load(name):
    return np.load('/home/kevxhk/work/L-gct-210/'+name)

# ---------- decomposition ----------
def parts(t):
    t = np.asarray(t); m = t.mean((-1, -2), keepdims=True)
    al = t.mean(-1)-m[..., 0]; be = t.mean(-2)-m[..., 0]
    g = t-m-al[..., :, None]-be[..., None, :]
    return m[..., 0, 0], al, be, g

def ab(al, be): return al[..., :, None]+be[..., None, :]

# ---------- orthonormal basis of V (sum-zero) in C^25 ----------
_M = np.eye(25)-np.ones((25, 25))/25
_u, _s, _vh = np.linalg.svd(_M)
VB = _vh[:24].real  # 24 x 25 real orthonormal

def hess_full(t, k):
    """25x25 Hessian of P_k at t (C^25 coordinates, row-major)."""
    t = np.asarray(t, complex).reshape(5, 5)
    N = 5
    a = np.exp(2j*np.pi*np.arange(N)/N)
    T = np.zeros((25, N, 5, 5), complex)
    for m in range(25):
        e = np.zeros(25); e[m] = 1; e = e.reshape(5, 5)
        for q in range(N): T[m, q] = t+a[q]*e
    _, G = Pk_grad(T.reshape(-1, 5, 5))
    G = G[:, k].reshape(25, N, 25)
    # coefficient of a^1: (1/N) sum_q G_q a_q^{-1}
    H = np.einsum('mqx,q->mx', G, a.conj())/N
    return H

def Qfull():
    return hess_full(np.zeros((5, 5)), 2).real

Q25 = Qfull()
QV = VB@Q25@VB.T  # 24x24 nondegenerate
QVi = np.linalg.inv(QV)

def toV(B):
    B = np.asarray(B).reshape(-1, 25); return B@VB.T  # coords (m,24)

def fromV(X):
    return (np.asarray(X)@VB).reshape(-1, 5, 5)

def MkV(t, k):
    """operator M with Q(M s, s') = H^k_t(s,s'), in V coords (24x24): M = QV^{-1} Hv."""
    H = hess_full(t, k); Hv = VB@H@VB.T
    return QVi@Hv

def rank(X, tol=1e-8):
    X = np.asarray(X)
    if X.size == 0: return 0
    s = np.linalg.svd(X, compute_uv=False)
    return int((s > tol*max(1, s[0])).sum())

def sv(X):
    return np.linalg.svd(np.asarray(X), compute_uv=False)

def orth(B):
    M = np.asarray(B, complex).reshape(len(B), -1)
    u, s, vh = np.linalg.svd(M, full_matrices=False)
    r = np.sum(s > 1e-9*s[0]); return vh[:r].reshape(r, 5, 5)

def resid(B, trials=40, seed=1):
    Qb = orth(B); rng = np.random.default_rng(seed)
    x = rng.normal(size=(trials, len(Qb)))+1j*rng.normal(size=(trials, len(Qb)))
    x /= np.linalg.norm(x, axis=1, keepdims=True)
    return np.abs(Pk(np.einsum('ri,iab->rab', x, Qb))[:, 1:]).max()

def inv(B):
    B = np.asarray(B); m, al, be, g = parts(B)
    return dict(dim=rank(B.reshape(len(B), -1)), rA=rank(al), rB=rank(be),
                r=rank(np.concatenate([al, be], 1)),
                d=rank(B.reshape(len(B), -1))-rank(np.concatenate([al, be], 1)))

def dcpart(B):
    """basis of L cap DC"""
    B = np.asarray(B); m, al, be, g = parts(B)
    AB = np.concatenate([al, be], 1)  # (m,10)
    u, s, vh = np.linalg.svd(AB.T)
    rk = int((s > 1e-9*max(1, s[0] if len(s) else 1)).sum())
    ker = vh[rk:].conj()
    return np.einsum('qk,kij->qij', ker, B)

def examples():
    ex = {'L080': L080(), 'ex1': ex1(), 'ex2': ex2(), 'rc45': rc45(), 'W5': W5()}
    for f in ['numerics/S4_r1d3.npy']:
        ex[f.split('/')[-1][:-4]] = load(f)
    return ex
