# leanfl r15: .ms chart + Singular mod-p cofactors -> Lean theorem  NAME_P : forall CommRing R, eqs -> exists g, 1 = p * g
# usage: python3 -I ms2lean.py NAME FILE.ms COF OUT.part   (fast dict polynomials; symmetric lift of cofactor coefficients)
import sys, re, time
name, msf, cof, out = sys.argv[1:5]
L = open(msf).read().split('\n'); V = [v.strip() for v in L[0].split(',')]; P = int(L[1]); idx = {v: i for i, v in enumerate(V)}
n = len(V)
def parse(s):
    s = s.replace(' ', '').replace('-', '+-')
    d = {}
    for t in s.split('+'):
        if not t: continue
        c = 1; e = [0]*n; sg = 1
        if t.startswith('-'): sg = -1; t = t[1:]
        for f in t.split('*'):
            if not f: continue
            if f[0].isdigit():
                if '/' in f: raise ValueError('rational')
                c *= int(f)
            else:
                m = re.match(r'([A-Za-z_][A-Za-z_0-9]*)(\^(\d+))?$', f)
                e[idx[m.group(1)]] += int(m.group(3) or 1)
        k = tuple(e); d[k] = d.get(k, 0) + sg*c
    return {k: v for k, v in d.items() if v}
eqs = [parse(x) for x in ''.join(L[2:]).split(',') if x.strip()]
cofs = [parse(x) for x in open(cof).read().split('\n') if x.strip()]
assert len(eqs) == len(cofs), (len(eqs), len(cofs))
sym = lambda c: (c % P) - P if (c % P) > P // 2 else c % P
eqs = [{k: sym(v) for k, v in f.items() if v % P} for f in eqs]
cofs = [{k: sym(v) for k, v in f.items() if v % P} for f in cofs]
t0 = time.time(); S = {}; prods = 0
for c, f in zip(cofs, eqs):
    for k1, v1 in c.items():
        for k2, v2 in f.items():
            k = tuple(a + b for a, b in zip(k1, k2)); S[k] = S.get(k, 0) + v1*v2; prods += 1
one = tuple([0]*n)
R = {k: -v for k, v in S.items() if v}; R[one] = R.get(one, 0) + 1
assert all(v % P == 0 for v in R.values())
G = {k: v // P for k, v in R.items() if v}
def lean(d):
    if not d: return '0'
    o = []
    for k, v in sorted(d.items(), reverse=True):
        mon = '*'.join(V[i] + ('^%d' % e if e > 1 else '') for i, e in enumerate(k) if e)
        s = ('%d' % abs(v)) + ('*' + mon if mon else '') if abs(v) != 1 or not mon else mon
        o.append(('- ' if v < 0 else '+ ') + s)
    r = ' '.join(o)
    return r[2:] if r.startswith('+ ') else '-' + r[2:]
binders = '(' + ' '.join(V) + ' : R)'
hyps = ' '.join('(h%d : %s = 0)' % (i, lean(f)) for i, f in enumerate(eqs))
lc = ' + '.join('(%s) * h%d' % (lean(c), i) for i, c in enumerate(cofs) if c)
txt = 'theorem %s_P {R : Type} [CommRing R] %s\n    %s :\n    ∃ g : R, 1 = %d * g :=\n  ⟨%s, by linear_combination %s⟩\n' % (name, binders, hyps, P, lean(G), lc)
open(out, 'w').write(txt)
print('%s: vars %d eqs %d eqterms %d cofterms %d products %d Sterms %d Gterms %d bytes %d (%.1fs)' % (name, n, len(eqs), sum(map(len, eqs)), sum(map(len, cofs)), prods, len(S), len(G), len(txt), time.time() - t0))
