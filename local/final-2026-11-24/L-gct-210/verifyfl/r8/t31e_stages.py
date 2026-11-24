import sys, os, subprocess, time, re; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""t31e_stages.py -- staged subsystem cut for gen_t31e (split B of [T31], eigen-normalised) and for gen_n2 split A (chi_1 l^T).
   Generators are indexed 0 = Z, 1.. = Y_k.  A stage is a set S of generator indices; it uses
     (coefficient equations whose x-monomial lies in S) + (extra equations whose variables all occur in those equations or are
      variables 'owned' by S) + (GBs of all earlier stages S' c S).
   Every polynomial used lies in the ideal of the full system, so UNIT at any stage => the full system is UNIT.
   usage: python3 -I t31e_stages.py E|A P MSPEC KS OUTPREFIX "Z;0;1;Z0;Z1;01;Z01" [timeout]
          (E: gen_t31e with Y_k, k in KS;  A: gen_n2 zsmode ('R1','chi1',0), stage a (KS=12) or b (KS=123); labels: Z = 0, digit d = Y_d)"""
import exactlib as X, subcut
kind, p, mspec, ks, out, spec = sys.argv[1], int(sys.argv[2]), sys.argv[3], [int(c) for c in sys.argv[4]], sys.argv[5], sys.argv[6]
tmo = float(sys.argv[7]) if len(sys.argv) > 7 and not sys.argv[7].startswith('gfac') else 1500
if kind.startswith('B0G'):                   # split B0 without the eigen form: kind B0G; generators Z, Y_1 ('1'), Y_2 ('2'); use with gfac=
    import gen_t31b0g
    names, eqs, extra, B = gen_t31b0g.build(p, mspec, 2, keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0R2:'):                # rank-two W structured (R10.7): kind M0R2:c1/c2/scell
    import gen_m0a
    pr_ = kind[5:].split('/')
    names, eqs, extra, B = gen_m0a.build_alpha_r2s(p, pr_[0], pr_[1], int(pr_[2]), keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0RS:'):                # rank-one W structured (R10.6): kind M0RS:vchart/nzero/scell[/nchart,nchart]
    import gen_m0a
    pr_ = kind[5:].split('/'); nch = tuple(pr_[3].split(',')) if len(pr_) > 3 else ()
    names, eqs, extra, B = gen_m0a.build_alpha_r1s(p, pr_[0], int(pr_[1]), int(pr_[2]), nch, keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0S:'):                 # m0 case (alpha), rank-two W, plane-adapted form (R10.2): kind M0S:INF/scell
    import gen_m0a
    a_, b_ = kind[4:].split('/'); inf = set() if a_ in ('', 'x') else {int(ch) for ch in a_}
    names, eqs, extra, B = gen_m0a.build_alpha_s(p, inf, int(b_), keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0N:'):                 # m0 case (alpha), rank-two W, explicit normal form (R9.6): kind M0N:INF
    import gen_m0a
    spec_ = kind[4:].split('/'); inf = set() if spec_[0] in ('', 'x') else {int(ch) for ch in spec_[0]}
    sg = None if len(spec_) == 1 else [1 if ch == '+' else -1 for ch in spec_[1]]       # M0N:INF/+-+ fixes e_1, e_2, e_3
    names, eqs, extra, B = gen_m0a.build_alpha_nf(p, inf, keyed=True, signs=sg)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0R1:'):                 # m0 case (alpha), rank-one W: kind M0R1:w or M0R1:c3
    import gen_m0a
    names, eqs, extra, B = gen_m0a.build_alpha_r1(p, kind[5:], keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0K:'):                  # m0 case (alpha), (k,t)-parametrised W: kind M0K:INF (INF digits among 0..3 or 'x' for none)
    import gen_m0a
    inf = set() if kind[4:] in ('', 'x') else {int(ch) for ch in kind[4:]}
    names, eqs, extra, B = gen_m0a.build_alpha_kt(p, inf, keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('M0A:'):                  # m0 = (1,1,1,1,-4), split A case (alpha): kind M0A:cell; generators Zs, Y_1 ('1'), Y_2 ('2')
    import gen_m0a
    names, eqs, extra, B = gen_m0a.build_alpha(p, int(kind[4:]), keyed=True)
    gidx = {'Z': 0, '1': 1, '2': 2}
elif kind.startswith('B1:'):                   # split B1, three-column normal form: kind B1:xcell[:omchart]; generators Z, Y3 ('3'), Y1 ('1')
    import gen_t31b1
    parts = kind.split(':'); xom = parts[1].startswith('w'); xc = int(parts[1][1:] if xom else parts[1]); oc = int(parts[2]) if len(parts) > 2 else None
    names, eqs, extra, B = gen_t31b1.build(p, mspec, xc, oc, keyed=True, xomega=xom)      # B1:wR:I -> s(Y3) = omega exactly, s(Y1) = b_R
    gidx = {'Z': 0, '3': 1, '1': 2}
elif kind.startswith('E'):
    import gen_t31e
    om = None if kind == 'E' else ('zero' if kind == 'E0' else ('ne', int(kind[2:])))      # E, E0, E11/E12/E13
    names, eqs, extra, B = gen_t31e.build(p, mspec, ks, keyed=True, omega=om)
    gf = [a for a in sys.argv[8:] if a.startswith('gfac=')]
    if gf:                                   # B0 component: add g(L(Z)), g = factor I of the eliminant, L = the random linear form
        import sympy as sp
        ffile, idx, lfile = gf[0][5:].split(':')
        g = open(ffile).read().split('\n')[int(idx)]; lin = open(lfile).read().strip()
        syms = {n: sp.Symbol(n) for n in names}
        expr = sp.expand(sp.sympify(g.replace('^', '**'), locals={'LL': sp.Symbol('LL')}).subs(sp.Symbol('LL'), sp.sympify(lin, locals=syms)))
        P_ = sp.Poly(expr, *[syms[n] for n in names])
        q = {}
        for mon, c in P_.terms():
            key = tuple(sorted(i for i, e in enumerate(mon) for _ in range(e))); c = int(c) % p
            if c: q[key] = (q.get(key, 0) + c) % p
        extra = list(extra) + [q]
    gidx = {'Z': 0}; gidx.update({str(k): 1 + i for i, k in enumerate(ks)})
else:
    import gen_n2
    cell = -1
    if kind.startswith('AC:'): zm = 'A'; cell = int(kind[3:])                      # general split A: echelon cell + <z_P0,z_P0> = 0
    else: zm = ('R1', 'chi1', 0) if kind == 'A' else ('R1', kind.split(':')[1], 2)  # kind 'A' or 'R2:ab' / 'R2:z1' / 'R2:z2'
    names, eqs, extra = gen_n2.build(p, mspec, cell, 'a' if len(ks) == 2 else 'b', keyed=True, zsmode=zm)
    gidx = {'Z': 0}; gidx.update({str(k): i for i, k in enumerate(ks, 1)})
# variables owned by each generator: those occurring in its matrix entries (computed from single-generator coefficient equations
# is not enough), so take them from the x-monomials of degree 1 in that generator ... simpler: from the equations keyed by x_g^d
def vars_of(polys): return {v for q in polys for mon in q for v in mon}
if kind.startswith('B0G'):
    gf = [a for a in sys.argv[8:] if a.startswith('gfac=')]
    if gf:
        import sympy as sp
        ffile, idx, lfile = gf[0][5:].split(':')
        g = open(ffile).read().split('\n')[int(idx)]; lin = open(lfile).read().strip()
        syms = {n: sp.Symbol(n) for n in names}
        expr = sp.expand(sp.sympify(g.replace('^', '**'), locals={'LL': sp.Symbol('LL')}).subs(sp.Symbol('LL'), sp.sympify(lin, locals=syms)))
        P_ = sp.Poly(expr, *[syms[n] for n in names]); q = {}
        for mon, c in P_.terms():
            key = tuple(sorted(i for i, e in enumerate(mon) for _ in range(e))); c = int(c) % p
            if c: q[key] = (q.get(key, 0) + c) % p
        extra = list(extra) + [q]
own = {}
for g in set(gidx.values()):
    own[g] = vars_of([e for (i, xm), e in eqs.items() if e and set(xm) == {X.XOFF + g}])
stages = []
ng = len(set(gidx.values()))
for lab in spec.split(';'):
    if lab.startswith('d'):                  # degree-vector stage, e.g. d4100 = x_Z-degree <= 4, x_1 <= 1, x_2 = x_3 = 0
        T = [int(c) for c in lab[1:]]; assert len(T) == ng
        stages.append((lab, [g for g in range(ng) if T[g] > 0], T))
    else:
        S = sorted({gidx[c] for c in lab}); stages.append((lab, S, [4 if g in S else 0 for g in range(ng)]))
gbs = []
for lab, S, T in stages:
    def okm(xm): return all(xm.count(X.XOFF + g) <= T[g] for g in range(ng))
    polys = [e for (i, xm), e in eqs.items() if e and okm(xm)]
    allowed = set().union(*[own[g] for g in S]) | vars_of(polys)
    allowed |= {i for i, nmv in enumerate(names) if nmv in ('uom', 'unz', 'u', 'ual')}     # Rabinowitsch variables: always allowed
    polys += [q for q in extra if vars_of([q]) <= allowed]
    prev = [g for (T0, G) in gbs if all(a <= b for a, b in zip(T0, T)) for g in G]
    fn = '%s_%s.ms' % (out, lab); vn = subcut.used_names(names, polys, prev)
    with open(fn, 'w') as f:
        f.write(','.join(vn) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + prev) + '\n')
    try:
        G, dt = subcut.msolve(fn, tmo)
    except Exception as ex:
        print('stage %s: msolve FAILED/TIMEOUT (%s)' % (lab, type(ex).__name__), flush=True); print('VERDICT %s %s KS=%s: FAIL at %s' % (kind, mspec, sys.argv[4], lab)); sys.exit()
    print('stage %s: %d polys + %d inherited, %d vars -> GB %d elements (%.1fs)%s' % (lab, len(polys), len(prev), len(vn), len(G), dt, '  UNIT' if G == ['1'] else ''), flush=True)
    gbs.append((T, G))
    if G == ['1']: print('VERDICT %s %s KS=%s: UNIT (at stage %s)' % (kind, mspec, sys.argv[4], lab)); sys.exit()
print('VERDICT %s %s KS=%s: NONUNIT' % (kind, mspec, sys.argv[4]))
