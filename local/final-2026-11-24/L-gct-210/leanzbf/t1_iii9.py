# F configurations: which non-passing patterns occur on their pair-12 transversals; class-size profiles
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_iii7.py').read().split('st = Counter(); seen = set()')[0])
from collections import Counter
pat = Counter(); prof = Counter(); seen = set(); npt = Counter()
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            key = (s12[1], s13[1], s23[1])
            if key in seen: continue
            seen.add(key)
            L12, L13, L23 = key
            if any(passes(a, b, c, T) for (_, a, b, c) in orders(L12, L13, L23) for T in transversals(a)): continue
            ps = set()
            for T in transversals(L12):
                ps.add((tuple(L13[m] for m in T), tuple(L23[m] for m in T)))
            npt[len(ps)] += 1
            for x in ps: pat[x] += 1
            sz = lambda L: tuple(sum(1 for m in cols if L[m] == v) for v in (1, 2, 3))
            prof[(sz(L12), sz(L13), sz(L23))] += 1
print('F configs', len([1 for _ in range(1)]) and sum(prof.values()))
print('distinct NP patterns used:', len(pat))
for k, v in sorted(pat.items()): print('  ', k, v)
print('patterns per config:', dict(npt))
print('class-size profiles (corner, Q2, Q3) for 12/13/23:', len(prof))
for k, v in sorted(prof.items()): print('  ', k, v)
