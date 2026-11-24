"""check of the degree-2 identities used in LEMMA RED-p (exact integer arithmetic at random integer matrices):
   column-centred Y:  [t^2] perm(J_4 + t Y^(j)) = Q - <s,s> - 2 q_j,  q_j = <y_j,y_j> - <s,y_j>,  Q = sum_a <y_a,y_a>, s = row sums;
   doubly centred Y: the same with s = 0."""
import itertools, random
def perm(M):
    n = len(M); return sum(eval('*'.join('M[%d][%d]' % (i, f[i]) for i in range(n))) for f in itertools.permutations(range(n)))
def deg2(Y, j):
    # perm(J + tA) = sum_k (4-k)! t^k P_k(A); the t^2 coefficient = 2 * P_2(A); compute P_2 directly
    A = [[Y[a][c] for c in range(5) if c != j] for a in range(4)]
    P2 = 0
    for r in itertools.combinations(range(4), 2):
        for c in itertools.combinations(range(4), 2):
            P2 += A[r[0]][c[0]] * A[r[1]][c[1]] + A[r[0]][c[1]] * A[r[1]][c[0]]
    return 2 * P2
rnd = random.Random(5); bad = 0
for trial in range(200):
    Y = [[rnd.randint(-9, 9) for c in range(5)] for a in range(4)]
    for c in range(5): Y[3][c] = -sum(Y[a][c] for a in range(3))          # column sums 0
    if trial % 2:                                                          # doubly centred: also row sums 0
        Y = [[rnd.randint(-9, 9) for c in range(4)] for a in range(3)]
        Y = [row + [-sum(row)] for row in Y]; Y.append([-sum(Y[a][c] for a in range(3)) for c in range(5)])
    s = [sum(Y[a]) for a in range(4)]; col = lambda j: [Y[a][j] for a in range(4)]
    ip = lambda u, v: sum(x * y for x, y in zip(u, v))
    Q = sum(ip(col(c), col(c)) for c in range(5))
    for j in range(5):
        if deg2(Y, j) != Q - ip(s, s) - 2 * (ip(col(j), col(j)) - ip(s, col(j))): bad += 1
print('degree-2 identity: %d mismatches in 1000 (column, matrix) pairs' % bad)
