import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/repr")
import numpy as np
from core import B25, T25
exec(open('/home/kevxhk/work/L-gct-210/repr/nine.py').read().split('Bm = np.array(basis)')[0])
Bm = np.array(basis)
one = np.ones(25)
rows = [one]
for i in range(9):
    rows.append(B25 @ Bm[i])
    for j in range(i, 9):
        rows.append(np.einsum('abc,a,b->c', T25, Bm[i], Bm[j]))
A = np.array(rows)
s = np.linalg.svd(A, compute_uv=False)
print('first-order extension space dim (incl L):', 25 - np.sum(s > 1e-9))
U, s, Vt = np.linalg.svd(A)
E = Vt[-10:].conj()  # basis of E (complex): null space of A
# component of E outside span(L9)
P = Bm.T @ np.linalg.pinv(Bm.T)
y = E.T[:, np.argmax(np.linalg.norm(E.T - P @ E.T, axis=0))]
y = y - P @ y; y /= np.linalg.norm(y)
print('Q(y,y)', y @ B25 @ y, 'max|C(l,y,y)|', max(abs(np.einsum('abc,a,b,c->', T25, Bm[i], y, y)) for i in range(9)), 'C(y,y,y)', np.einsum('abc,a,b,c->', T25, y, y, y))
print('y (5x5):'); print(np.round(y.reshape(5, 5), 3))
