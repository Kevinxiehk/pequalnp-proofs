import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
import numpy as np
from core import *
w = w3
def E(i, j, v=1.0):
    M = np.zeros((5, 5), complex); M[i, j] = v; return M
def skeleton():
    B = [E(3, j) - E(3, 4) for j in range(4)]
    M = np.zeros((5, 5), complex); M[:3, 4] = 1; M[4, 4] = -3; B.append(M); return B
def ex1():
    M1 = np.zeros((5, 5), complex); M2 = np.zeros((5, 5), complex)
    for i in range(3):
        M1[i, 0] = w ** i; M1[i, 1] = -w ** i; M2[i, 2] = w ** (2 * i); M2[i, 3] = -w ** (2 * i)
    return np.array([M1, M2] + skeleton())
def ex2():
    B = []
    for c in (0, 1):
        M = np.zeros((5, 5), complex); M[:3, c] = w ** np.arange(3); B.append(M)
    return np.array(B + skeleton())
def ex3():
    M1 = np.zeros((5, 5), complex); M2 = np.zeros((5, 5), complex)
    for i in range(3):
        M1[i, 2] = w ** (2 * i); M1[i, 3] = -w ** (2 * i); M2[i, 2] = w ** i; M2[i, 3] = w ** i
    return np.array([M1, M2] + skeleton())
def fam(s, p=0, q=3):
    A = np.array([2, -1, -1.]); b = np.array([0, 1, -1.])
    M1 = np.zeros((5, 5), complex); M2 = np.zeros((5, 5), complex)
    M1[:3, p] = A; M1[:3, q] = s * b; M2[:3, p] = -3 * b; M2[:3, q] = s * A
    return np.array([M1, M2] + skeleton())
def L080():
    B = [E(4, a) - E(4, 3) for a in range(3)] + [E(b, 4) - E(4, 4) for b in range(4)]
    return np.array(B)
def R3():
    B = []
    for c in range(3):
        M = np.zeros((5, 5), complex); M[:4, c] = chi(1); B.append(M)
    B += [E(4, j) - E(4, 4) for j in range(4)]
    return np.array(B)
def L9T():
    B = []
    for c in range(5):
        M = np.zeros((5, 5), complex); M[:4, c] = chi(1); B.append(M)
    B += [E(4, j) - E(4, 4) for j in range(4)]
    return np.array(B)
def blk42():
    return np.load('/home/kevxhk/work/L-gct-210/numerics/r2/F_e2_blk_0.npy')
EX = {'L080': L080, 'ex1': ex1, 'ex2': ex2, 'ex3': ex3, 'fam(0.6+1.4i)': lambda: fam(0.6 + 1.4j), 'fam(4)': lambda: fam(4.0),
      'fam(0)': lambda: fam(0.0), 'R3': R3, 'blk42': blk42}
