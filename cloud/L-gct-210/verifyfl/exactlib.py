"""exactlib.py -- common code of the exact generators gen_n1.py ([DC-k]), gen_n2.py ([T31]), gen_n3.py ([T22]).
Pure Python, modular polynomial arithmetic (same idea as coord/local/results/VF-A/gen.py), msolve input files.

Polynomials: dict {monomial: coeff mod p}; a monomial is a sorted tuple of variable ids (with repetition); () is the constant 1.
Unknowns have ids 0..NU-1; the auxiliary variables x_r (coefficients of the generators) have ids XOFF + r.

Mathematics (COMPUTE-verifyfl.md section 0): for a 4x5 matrix Y, C_j(Y) = perm(J_4 + Y with column j removed);
a space has "defect in C m" iff R_i(Y) := sum_j W_ij (C_j(Y) - 24) = 0 on it, W = a basis of {w : sum_j w_j m_j = 0}.
For generators B_1..B_k (matrices of polynomials in the unknowns) the equations are ALL coefficients, as polynomials in x_1..x_k,
of R_i(x_1 B_1 + ... + x_k B_k)."""
import itertools, sys
XOFF = 100000
FACT = {0: 1, 1: 1, 2: 2, 3: 6, 4: 24}

# ---------- arithmetic mod p ----------
def sqrtm(a, p):
    a %= p
    if a == 0: return 0
    assert pow(a, (p - 1) // 2, p) == 1, 'non-residue: %d mod %d' % (a, p)
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1: z += 1
    M, c, t, R = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1: tt = tt * tt % p; i += 1
        b = pow(c, 1 << (M - i - 1), p); M, c, t, R = i, b * b % p, t * b * b % p, R * b % p
    return R
def inv(a, p): return pow(a % p, p - 2, p)
class Consts:
    """i, w (primitive cube root of unity), sqrt3 mod p; p must be 1 mod 12."""
    def __init__(self, p):
        assert p % 12 == 1; self.p = p
        self.I = sqrtm(-1, p); self.s3 = sqrtm(3, p); self.w = (-1 + self.I * self.s3) * inv(2, p) % p
        assert (self.w * self.w + self.w + 1) % p == 0
        self.chi1 = [1, self.I, p - 1, (-self.I) % p]; self.chi2 = [1, p - 1, 1, p - 1]; self.chi3 = [1, (-self.I) % p, p - 1, self.I]
        self.zeta = [1, self.w, self.w * self.w % p, 0]; self.zetab = [1, self.w * self.w % p, self.w, 0]; self.h = [1, 1, 1, p - 3]
    def tok(self, t):
        """parse one entry of m: integer, 'w', 'w2', 'i', '-i', or a product like '2*w'."""
        p = self.p; v = 1
        for f in t.split('*'):
            f = f.strip(); neg = f.startswith('-'); f = f.lstrip('-')
            x = {'w': self.w, 'w2': self.w * self.w % p, 'i': self.I}.get(f)
            if x is None: x = int(f) % p
            v = v * (p - x if neg else x) % p
        return v
PRESETS = {'m12m3': '1,2,-3,0,0', 'm11m2': '1,1,-2,0,0', 'm2m1m1': '2,-1,-1,0,0', 'iso': '1,w,w2,0,0', 'two': '1,-1,0,0,0',
           'p4a': '1,2,3,-6,0', 'p4b': '1,2,-4,1,0', 'p4c': '1,1,1,-3,0', 'p4d': '1,1,-1,-1,0', 'p4iso': '1,i,-1,-i,0',
           'p5a': '1,2,3,-1,-5', 'p5b': '1,1,1,1,-4', 'p5c': '2,2,2,-3,-3'}
def parse_m(spec, cs):
    """returns (m, W): m = list of 5 residues, or None for spec 'SL' (strongly level: all C_j = 24, W = identity)."""
    if spec == 'SL': return None, [[1 if a == b else 0 for b in range(5)] for a in range(5)]
    spec = PRESETS.get(spec, spec); p = cs.p
    m = [cs.tok(t) for t in spec.split(',')]; assert len(m) == 5 and sum(m) % p == 0 and any(m)
    P = [j for j in range(5) if m[j]]; W = []
    for j in range(5):
        if not m[j]: W.append([1 if a == j else 0 for a in range(5)])
    p0 = P[0]
    for j in P[1:]:
        r = [0] * 5; r[j] = m[p0]; r[p0] = (-m[j]) % p; W.append(r)
    for r in W: assert sum(a * b for a, b in zip(r, m)) % p == 0
    assert len(W) == 4
    return m, W

# ---------- polynomials ----------
def padd(a, b, p, cb=1):
    r = dict(a)
    for k, v in b.items():
        x = (r.get(k, 0) + cb * v) % p
        if x: r[k] = x
        elif k in r: del r[k]
    return r
def pmul(a, b, p):
    r = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(sorted(ka + kb)); r[k] = (r.get(k, 0) + va * vb) % p
    return {k: v for k, v in r.items() if v}
def pconst(c, p): return {(): c % p} if c % p else {}
def pvar(i): return {(i,): 1}
def peval(q, val, p):
    """val: dict var id -> residue"""
    t = 0
    for k, c in q.items():
        for v in k: c = c * val[v] % p
        t += c
    return t % p

class Vars:
    def __init__(self): self.names = []
    def new(self, name): self.names.append(name); return pvar(len(self.names) - 1)
    def __len__(self): return len(self.names)

# ---------- parametrisations of matrices ----------
def dc_matrix(co, p):
    """co: 12 polynomials = coordinates c[4a+q] (a < 3, q < 4) in the basis (e_a - e_3)(e_q - e_4)^T of the doubly centred 4x5 matrices.
    Entry (a,q) = c[4a+q] for a < 3, q < 4; last column and last row are minus the sums."""
    M = [[{} for _ in range(5)] for _ in range(4)]
    for a in range(3):
        for q in range(4):
            c = co[4 * a + q]; M[a][q] = dict(c)
            M[a][4] = padd(M[a][4], c, p, -1); M[3][q] = padd(M[3][q], c, p, -1); M[3][4] = padd(M[3][4], c, p)
    return M
def col_matrix(co, cols, p):
    """matrices with zero column sums supported on the columns 'cols': co[3*t + a] = entry (a, cols[t]), a < 3; row 3 = minus the sum."""
    M = [[{} for _ in range(5)] for _ in range(4)]
    for t, q in enumerate(cols):
        for a in range(3):
            c = co[3 * t + a]; M[a][q] = dict(c); M[3][q] = padd(M[3][q], c, p, -1)
    return M
def dcsub_matrix(co, cols, p):
    """doubly centred matrices supported on the columns 'cols' (len >= 2): co[3*t + a] = entry (a, cols[t]) for t < len(cols)-1, a < 3."""
    M = [[{} for _ in range(5)] for _ in range(4)]; last = cols[-1]
    for t, q in enumerate(cols[:-1]):
        for a in range(3):
            c = co[3 * t + a]; M[a][q] = dict(c)
            M[a][last] = padd(M[a][last], c, p, -1); M[3][q] = padd(M[3][q], c, p, -1); M[3][last] = padd(M[3][last], c, p)
    return M
def madd_const_col(M, vec, col, p):
    """add the constant/polynomial vector vec (list of 4 polynomials) to column col"""
    for a in range(4): M[a][col] = padd(M[a][col], vec[a], p)
    return M
def echelon_rows(n, pivots, V, prefix):
    """reduced row echelon cell of Gr(k,n): row r has 1 at pivots[r], 0 at the other pivots and at all positions < pivots[r];
    the remaining positions are new unknowns.  Returns the list of k coordinate lists (polynomials)."""
    rows = []
    for r, pr in enumerate(pivots):
        row = []
        for d in range(n):
            if d == pr: row.append({(): 1})
            elif d in pivots or d < pr: row.append({})
            else: row.append(V.new('%s%d_%d' % (prefix, r, d)))
        rows.append(row)
    return rows
def cells(n, k): return list(itertools.combinations(range(n), k))

# ---------- the equations ----------
def equations(B, W, p, keyed=False):
    """B: list of k generator matrices (4x5, entries polynomials in the unknowns).  Returns the list of all nonzero coefficient polynomials
    of R_i(sum_r x_r B_r), i over the rows of W, and the number of x-monomials seen.  Linear coefficients are included (they vanish
    identically when all generators have zero column sums)."""
    k = len(B)
    E = [[{} for _ in range(5)] for _ in range(4)]
    for r in range(k):
        xr = (XOFF + r,)
        for a in range(4):
            for c in range(5):
                for mon, v in B[r][a][c].items(): E[a][c][mon + xr] = v
    C = []
    for j in range(5):
        cols = [c for c in range(5) if c != j]; tot = {}
        for d in (1, 2, 3, 4):
            f = FACT[4 - d]
            for rows in itertools.combinations(range(4), d):
                for cs in itertools.combinations(cols, d):
                    for perm in itertools.permutations(cs):
                        fac = [E[rows[t]][perm[t]] for t in range(d)]
                        if any(not q for q in fac): continue
                        pr = fac[0]
                        for q in fac[1:]: pr = pmul(pr, q, p)
                        for mon, v in pr.items():
                            x = (tot.get(mon, 0) + f * v) % p
                            if x: tot[mon] = x
                            elif mon in tot: del tot[mon]
        C.append(tot)
    eqs = {}
    for i, wr in enumerate(W):
        for j in range(5):
            if not wr[j]: continue
            for mon, v in C[j].items():
                cut = len(mon)
                while cut > 0 and mon[cut - 1] >= XOFF: cut -= 1
                key = (i, mon[cut:]); e = eqs.setdefault(key, {}); u = mon[:cut]
                x = (e.get(u, 0) + wr[j] * v) % p
                if x: e[u] = x
                elif u in e: del e[u]
    if keyed: return eqs
    return [e for e in eqs.values() if e], len(eqs)

# ---------- output ----------
def fmt_poly(q, names):
    terms = []
    for k, v in sorted(q.items()):
        mon = []
        for vid in sorted(set(k)):
            e = k.count(vid); mon.append('%s^%d' % (names[vid], e) if e > 1 else names[vid])
        terms.append(str(v) + ('*' + '*'.join(mon) if mon else ''))
    return '+'.join(terms) if terms else '0'
def write_msolve(path, names, p, polys):
    """msolve input: variables, characteristic, polynomials separated by commas (same format as VF-A)."""
    if not names: names = ['dummy']
    with open(path, 'w') as f:
        f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join(fmt_poly(q, names) for q in polys) + '\n')
def trivially_unit(polys):
    return any(len(q) == 1 and () in q for q in polys)

# ---------- linear algebra mod p (for the self-tests) ----------
def rref(rows, p):
    rows = [list(r) for r in rows]; piv = []; r = 0; n = len(rows[0])
    for c in range(n):
        s = next((t for t in range(r, len(rows)) if rows[t][c] % p), None)
        if s is None: continue
        rows[r], rows[s] = rows[s], rows[r]; iv = inv(rows[r][c], p); rows[r] = [x * iv % p for x in rows[r]]
        for t in range(len(rows)):
            if t != r and rows[t][c] % p:
                f = rows[t][c]; rows[t] = [(x - f * y) % p for x, y in zip(rows[t], rows[r])]
        piv.append(c); r += 1
        if r == len(rows): break
    return rows[:r], piv
def outer(u, v, p): return [[u[a] * v[c] % p for c in range(5)] for a in range(4)]
def msum(A, B, p, cb=1): return [[(A[a][c] + cb * B[a][c]) % p for c in range(5)] for a in range(4)]
def dc_coords(M, p):
    for a in range(4): assert sum(M[a]) % p == 0, 'row sum'
    for c in range(5): assert sum(M[a][c] for a in range(4)) % p == 0, 'column sum'
    return [M[a][q] % p for a in range(3) for q in range(4)]

def run_msolve(path, out=None, timeout=120):
    """runs msolve -g 2; returns ('UNIT' | 'NONUNIT' | 'TIMEOUT' | 'ERROR', number of basis elements or None, seconds)"""
    import subprocess, time, os
    out = out or path + '.gb'; t0 = time.time()
    try:
        r = subprocess.run(['/home/claude/tools/gb/msolve', '-g', '2', '-f', path, '-o', out], capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', None, time.time() - t0
    dt = time.time() - t0
    if not os.path.exists(out): return 'ERROR', None, dt
    s = open(out).read(); n = None
    for line in s.splitlines():
        if 'length of basis' in line:
            n = int(line.split(':')[1].split()[0])
    body = ''.join(l for l in s.splitlines() if not l.startswith('#')).replace(' ', '')
    unit = body.strip().rstrip(':') in ('[1]', '[1]:')
    if n is None: return 'ERROR', None, dt
    return ('UNIT' if unit else 'NONUNIT'), n, dt
