import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
import numpy as np
from lm import *
from examples import *
def Lprime(B, r):
    """L cap {row r = 0} as 4x5 matrices"""
    B = np.asarray(B, complex).reshape(len(B), 5, 5)
    u, s, vh = np.linalg.svd(B[:, r, :].T); rk = int(np.sum(s > 1e-9)); Ns = vh[rk:].conj().T
    return np.delete(np.einsum('ik,iab->kab', Ns, B), r, axis=1)
which = sys.argv[1] if len(sys.argv) > 1 and __name__ == "__main__" else ""
if which == 'k3':
    print('# k=3 random starts, full system'); h = run(3, 'cs', True, 6, 10, tmax=120); np.save('hits_k3.npy', np.array(h))
if which == 'plant3':
    for nm, r in (('ex1', 3), ('R3', 4), ('ex2', 3)):
        for noise in (0.05, 0.3):
            print(f'# planted {nm} L\' + noise {noise}'); run(3, 'cs', True, 2, 20, plant=Lprime(EX[nm](), r), noise=noise, tmax=40)
if which == 'k4':
    print('# k=4 random starts, full system (claim: no solution)'); run(4, 'cs', True, 5, 30, tmax=150)
if which == 'k4relax':
    print('# k=4 random starts, RELAXED system P2,P3 only (solutions exist: chi_1 (x) C^5 has dim 5)'); run(4, 'cs', False, 4, 40, tmax=120)
if which == 'k4plantrelax':
    Bp = np.array([np.outer(chi(1), np.eye(5)[c]) for c in range(4)])
    print('# k=4 planted chi_1 (x) C^4 + noise: relaxed system must return to a solution, full system must not')
    run(4, 'cs', False, 2, 50, plant=Bp, noise=0.2, tmax=60); run(4, 'cs', True, 2, 50, plant=Bp, noise=0.2, tmax=80)
if which == 'dc2':
    print('# DC k=2 full'); h = run(2, 'dc', True, 8, 60, tmax=100); np.save('hits_dc2.npy', np.array(h))
if which == 'dc3':
    print('# DC k=3 full (claim: none)'); run(3, 'dc', True, 6, 70, tmax=120)
    print('# DC k=3 relaxed (exist: chi_1 (x) Lambda)'); run(3, 'dc', False, 4, 80, tmax=50)
