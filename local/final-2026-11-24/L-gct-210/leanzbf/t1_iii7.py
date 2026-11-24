# exact-pattern dispatch analysis for (II,II,II): pass iff (l13, l23) on a pair-12 transversal (p,q,s) is one of the 98 generated patterns
import ast, itertools
from collections import Counter
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/t1_enum.py').read().split("random.seed(1)")[0])
PASS = set()
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t3p.log'):
    if line.startswith('(('):
        lab, x, sg, name = ast.literal_eval(line.strip()); PASS.add((lab, x))
II = [s for s in STR if s[0] == 'II']
sw = {1: 1, 2: 3, 3: 2}
def swap(lab): return tuple(sw[l] for l in lab)
def orders(L12, L13, L23):
    # yields (name, l12, l13, l23) for the 6 row orders (labels of ordered pairs)
    yield '123', L12, L13, L23
    yield '132', L13, L12, swap(L23)
    yield '213', swap(L12), L23, L13
    yield '231', L23, swap(L12), swap(L13)
    yield '312', swap(L13), swap(L23), L12
    yield '321', swap(L23), swap(L13), swap(L12)
def transversals(l12):
    P = [m for m in cols if l12[m] == 1]; Q = [m for m in cols if l12[m] == 2]; S = [m for m in cols if l12[m] == 3]
    return [(p, q, s) for p in P for q in Q for s in S]
def passes(l12, l13, l23, T):
    return (tuple(l13[m] for m in T), tuple(l23[m] for m in T)) in PASS
st = Counter(); seen = set()
for s12 in II:
    for s13 in II:
        for s23 in II:
            if not ratio_ok(s12[2], s13[2], s23[2]): continue
            key = (s12[1], s13[1], s23[1])
            if key in seen: continue
            seen.add(key)
            L12, L13, L23 = key
            Ts = transversals(L12)
            good0 = [T for T in Ts if passes(L12, L13, L23, T)]
            anyorder = any(passes(a, b, c, T) for (_, a, b, c) in orders(L12, L13, L23) for T in transversals(a))
            if not anyorder: st['F (no order works)'] += 1; continue
            st['killable'] += 1
            if len(good0) == len(Ts): st['all 12-transversals pass'] += 1
            elif good0:
                # every failing T has a one-point-replacement fix?
                fix1 = all(passes(L12, L13, L23, T) or any(passes(L12, L13, L23, T2) for T2 in Ts if sum(a != b for a, b in zip(T, T2)) == 1) for T in Ts)
                st['some 12-transversal passes; 1-swap fix for all' if fix1 else 'some pass; needs 2-swap'] += 1
            else:
                st['no 12-transversal passes (needs row reorder)'] += 1
print('distinct label configs', len(seen))
for k, v in sorted(st.items()): print(k, v)
