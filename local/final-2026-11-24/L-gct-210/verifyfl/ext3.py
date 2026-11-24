import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""calibrated extension test of Lemma SL on every known 3-dim strongly level space L':
   (cal) a random plane F in L' must extend (LM must find extensions); (test) L' itself must not extend."""
import numpy as np
from core import *
from examples import *
from lmrun import Lprime
from ext import ext_search
rng = np.random.default_rng(8)
spaces = {'L080^T': Lprime(np.transpose(L080(), (0, 2, 1)), 4), 'ex1': Lprime(ex1(), 3), 'ex2': Lprime(ex2(), 3), 'ex3': Lprime(ex3(), 3),
          'fam(0.6+1.4i)': Lprime(fam(0.6 + 1.4j), 3), 'fam(0)': Lprime(fam(0.0), 3), 'R3': Lprime(R3(), 4), 'blk42': Lprime(blk42(), 3)}
try:
    for i, B in enumerate(np.load('hits_k3.npy')): spaces['LMhit%d' % i] = B
except Exception as ex: print('no LM hits', ex)
for nm, Lp in spaces.items():
    assert rank(Lp) == 3 and sl_check(Lp) < 1e-9
    c = rng.normal(size=(2, 3)) + 1j * rng.normal(size=(2, 3)); F = np.einsum('ki,iab->kab', c, Lp)
    cal, n1 = ext_search(F, 6, 100, tmax=20)
    inL = 0
    for Y in cal:
        K = Lp.reshape(3, -1); coef, *_ = np.linalg.lstsq(K.T, Y.ravel(), rcond=None); inL += np.linalg.norm(K.T @ coef - Y.ravel()) < 1e-6
    tst, n2 = ext_search(Lp, 10, 200, tmax=30)
    print(f'{nm:14s} calibration (random plane of L\'): {len(cal)}/{n1} extensions found ({inL} inside L\');  L\' itself: {len(tst)}/{n2} extensions', flush=True)
