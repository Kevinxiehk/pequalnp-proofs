# configurations left by T3Rest (every pair-12 transversal non-passing): which row orders rescue them
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_iii7.py').read().split('st = Counter(); seen = set()')[0])
from collections import Counter
st = Counter(); seen = set()
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            key = (s12[1], s13[1], s23[1])
            if key in seen: continue
            seen.add(key)
            L12, L13, L23 = key
            if any(passes(L12, L13, L23, T) for T in transversals(L12)): continue
            ok = tuple(sorted(name for (name, a, b, c) in orders(L12, L13, L23) if any(passes(a, b, c, T) for T in transversals(a))))
            st[ok] += 1
for k, v in sorted(st.items()): print(k if k else 'F (no order)', v)
