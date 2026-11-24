# Generator: Lemma B (purely combinatorial on the six class Finsets) -> lean/zbf/r7_1.txt
# From the two transversal hypotheses of T3Rest2 (order 123 and 132) and the class witnesses, every column has one of the
# four types of orientation 1 or every column has one of the four types of orientation 2.
import itertools, ast
GEN = set()
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t3p.log'):
    if line.startswith('(('):
        lab, x, sg, name = ast.literal_eval(line.strip()); GEN.add((lab, x))
LAB = {'Q': 2, 'B': 3, 'C': 1}
SW = {'Q': 'B', 'B': 'Q', 'C': 'C'}
COLW = ['p', 'q', 's']
WZ = {'p': 1, 'q': 0, 's': 2}
def zval(st, sg): return {'Q': 0, 'B': 2, 'C': (1 if sg == 1 else 3)}[st]
# NP list exactly as in gen_t3d.py (same order -> same disjunction text)
def consistent_t(st13, st23):
    for s1 in (1, -1):
        for s2 in (1, -1):
            ks = {(zval(st13[m], s1) - zval(st23[m], s2) - WZ[m]) % 4 for m in COLW}
            if len(ks) == 1: return True
    return False
NP = []
for t13 in itertools.product('QBC', repeat=3):
    for t23 in itertools.product('QBC', repeat=3):
        if not consistent_t(dict(zip(COLW, t13)), dict(zip(COLW, t23))): continue
        l13 = tuple(LAB[a] for a in t13); l23 = tuple(LAB[a] for a in t23)
        if (l13, l23) in GEN: continue
        NP.append((t13, t23))
assert len(NP) == 26
NPSET = set(NP)
def atom(m, S, st):
    if st == 'Q': return f'{m} ∈ {S[0]}'
    if st == 'B': return f'{m} ∈ {S[1]}'
    return f'({m} ∉ {S[0]} ∧ {m} ∉ {S[1]})'
def disj_parts(sets13, sets23):
    parts = []
    for (t13, t23) in NP:
        at = []
        for k, m in enumerate(COLW):
            at.append(atom(m, sets13, t13[k])); at.append(atom(m, sets23, t23[k]))
        parts.append('(' + ' ∧ '.join(at) + ')')
    return parts
PARTS1 = disj_parts(('Q13', 'B13'), ('Q23', 'B23'))
PARTS2 = disj_parts(('Q12', 'B12'), ('B23', 'Q23'))
# a transversal (u corner, v Q, w B) of the distinguished pair is OK under Hall iff its pattern is in NP
def hall_ok(Su, Sv, Sw, order):
    if order == '123':
        t13 = (Su[1], Sv[1], Sw[1]); t23 = (Su[2], Sv[2], Sw[2])
    else:
        t13 = (Su[0], Sv[0], Sw[0]); t23 = (SW[Su[2]], SW[Sv[2]], SW[Sw[2]])
    return (t13, t23) in NPSET
def find_prune(K):
    # K: dict colname -> status (s12, s13, s23); find a transversal among K violating Hall (order 123 or 132)
    names = list(K)
    for order in ('123', '132'):
        role = 0 if order == '123' else 1
        for u, v, w in itertools.permutations(names, 3):
            if (K[u][role], K[v][role], K[w][role]) == ('C', 'Q', 'B'):
                if not hall_ok(K[u], K[v], K[w], order): return (order, u, v, w)
    return None
S27 = list(itertools.product('QBC', repeat=3))
# Hall cases for (p,q,s): statuses p=(C,..), q=(Q,..), s=(B,..) with the (13,23) pattern in NP
CASES = []
for (t13, t23) in NP:
    CASES.append({'p': ('C', t13[0], t23[0]), 'q': ('Q', t13[1], t23[1]), 's': ('B', t13[2], t23[2])})
def allowed(case):
    out = []
    for z in S27:
        K = dict(case); K['m'] = z
        if find_prune(K) is None: out.append(z)
    return out
O1 = {('C', 'C', 'C'), ('C', 'Q', 'Q'), ('Q', 'C', 'B'), ('B', 'B', 'C')}
O2 = {('C', 'C', 'C'), ('C', 'B', 'B'), ('Q', 'Q', 'C'), ('B', 'C', 'Q')}
ORD1 = [('C', 'C', 'C'), ('C', 'Q', 'Q'), ('Q', 'C', 'B'), ('B', 'B', 'C')]
ORD2 = [('C', 'C', 'C'), ('C', 'B', 'B'), ('Q', 'Q', 'C'), ('B', 'C', 'Q')]
# witnesses: tag -> (class index (0:12, 1:13, 2:23), status letter)
WIT = [('wa', 1, 'Q'), ('wb', 1, 'B'), ('wc', 1, 'C'), ('wd', 2, 'Q'), ('we', 2, 'B'), ('wf', 2, 'C')]
def refute(K, al, depth):
    for d in range(depth + 1):
        pl = refute_d(K, al, d)
        if pl: return pl
    return None
def refute_d(K, al, depth):
    # returns a proof plan: ('prune', t) or ('wit', tag, [(status, subplan)]) or None
    t = find_prune(K)
    if t: return ('prune', t)
    if depth == 0: return None
    for tag, ci, st in WIT:
        if tag in K: continue
        cand = [z for z in al if z[ci] == st]
        sub = []
        ok = True
        for z in cand:
            K2 = dict(K); K2[tag] = z
            pl = refute_d(K2, al, depth - 1)
            if pl is None: ok = False; break
            sub.append((z, pl))
        if ok: return ('wit', tag, sub)
    return None
# ---------------- Lean text ----------------
SETS = [('Q12', 'B12'), ('Q13', 'B13'), ('Q23', 'B23')]
def lits(v, S):
    out = []
    for k, st in enumerate(S):
        q, b = SETS[k]
        if st == 'Q': out += [f'{v} ∈ {q}', f'{v} ∉ {b}']
        elif st == 'B': out += [f'{v} ∉ {q}', f'{v} ∈ {b}']
        else: out += [f'{v} ∉ {q}', f'{v} ∉ {b}']
    return out
def conj(v, S): return ' ∧ '.join(lits(v, S))
def hn(v, i): return f'h{v}{i}'
def facts(cols): return ', '.join(hn(v, i) for v in cols for i in range(1, 7))
SIMPX = 'not_true_eq_false, not_false_eq_true, true_and, and_true, false_and, and_false, or_false, false_or, or_self, and_self'
def prune_lines(t):
    order, u, v, w = t
    if order == '123':
        call = f'Hall {u} {v} {w} {hn(u, 2)} {hn(u, 1)} {hn(v, 1)} {hn(w, 2)}'
    else:
        call = f'Hall2 {u} {v} {w} {hn(u, 4)} {hn(u, 3)} {hn(v, 3)} {hn(w, 4)}'
    return [f'have hD := {call}', f'simp [{facts([u, v, w])}] at hD']
def ornest(i, n, body):
    core = body if i == n - 1 else f'Or.inl {body}'
    for _ in range(i): core = f'Or.inr ({core})'
    return core
def plan_lines(plan, K, al):
    if plan[0] == 'prune': return prune_lines(plan[1])
    _, tag, sub = plan
    L = [f'rcases B1 {tag} with ' + ' | '.join('h' for _ in al)]
    for z in al:
        match = [pl for (zz, pl) in sub if zz == z]
        if not match:
            br = [f'simp [{hn(tag, 3)}, {hn(tag, 4)}, {hn(tag, 5)}, {hn(tag, 6)}] at h']
        else:
            K2 = dict(K); K2[tag] = z
            br = [f'obtain ⟨{", ".join(hn(tag, i) for i in range(1, 7))}⟩ := h'] + plan_lines(match[0], K2, al)
        L += ['· ' + br[0]] + ['  ' + x for x in br[1:]]
    return L
def status_split(v, k, cont):
    q, b = SETS[k]
    i1, i2 = 2 * k + 1, 2 * k + 2
    out = [f'by_cases {hn(v, i1)} : {v} ∈ {q}']
    sq = cont('Q')
    hqb = ['hQB12', 'hQB13', 'hQB23'][k]
    out += [f'· have {hn(v, i2)} : {v} ∉ {b} := {hqb} {v} {hn(v, i1)}'] + ['  ' + x for x in sq]
    out += [f'· by_cases {hn(v, i2)} : {v} ∈ {b}']
    sb = cont('B'); sc = cont('C')
    out += ['  · ' + sb[0]] + ['    ' + x for x in sb[1:]]
    out += ['  · ' + sc[0]] + ['    ' + x for x in sc[1:]]
    return out
def b1_lines(case, al):
    L = ['have B1 : ∀ m : Fin 5,']
    ds = ['(' + conj('m', z) + ')' for z in al]
    for i, d in enumerate(ds):
        L.append('    ' + d + (' ∨' if i < len(ds) - 1 else ' := by'))
    def rec(k, S):
        if k == 3:
            z = tuple(S)
            if z in al:
                return [f'exact {ornest(al.index(z), len(al), "⟨" + ", ".join(hn("m", i) for i in range(1, 7)) + "⟩")}']
            K = dict(case); K['m'] = z
            t = find_prune(K)
            assert t
            return prune_lines(t)
        return status_split('m', k, lambda st: rec(k + 1, S + [st]))
    body = ['intro m'] + rec(0, [])
    L += ['  ' + x for x in body]
    return L
def case_facts(case, atoms):
    L = []
    L += ['have hp1 : p ∉ Q12 := hpQ', 'have hp2 : p ∉ B12 := hpB',
          'have hq1 : q ∈ Q12 := hqQ', 'have hq2 : q ∉ B12 := hQB12 q hqQ',
          'have hs1 : s ∉ Q12 := fun h => hQB12 s h hsB', 'have hs2 : s ∈ B12 := hsB']
    for v in COLW:
        for k in (1, 2):
            st = case[v][k]; a = atoms[(v, k)]
            q, b = SETS[k]; i1, i2 = 2 * k + 1, 2 * k + 2
            hqb = ['hQB12', 'hQB13', 'hQB23'][k]
            if st == 'Q':
                L += [f'have {hn(v, i1)} : {v} ∈ {q} := {a}', f'have {hn(v, i2)} : {v} ∉ {b} := {hqb} {v} {a}']
            elif st == 'B':
                L += [f'have {hn(v, i2)} : {v} ∈ {b} := {a}', f'have {hn(v, i1)} : {v} ∉ {q} := fun h => {hqb} {v} h {a}']
            else:
                L += [f'have {hn(v, i1)} : {v} ∉ {q} := {a}.1', f'have {hn(v, i2)} : {v} ∉ {b} := {a}.2']
    return L
WITF = '''have hwa3 : wa ∈ Q13 := hwaQ
  have hwa4 : wa ∉ B13 := hQB13 wa hwaQ
  have hwb3 : wb ∉ Q13 := fun h => hQB13 wb h hwbB
  have hwb4 : wb ∈ B13 := hwbB
  have hwc3 : wc ∉ Q13 := hwcQ
  have hwc4 : wc ∉ B13 := hwcB
  have hwd5 : wd ∈ Q23 := hwdQ
  have hwd6 : wd ∉ B23 := hQB23 wd hwdQ
  have hwe5 : we ∉ Q23 := fun h => hQB23 we h hweB
  have hwe6 : we ∈ B23 := hweB
  have hwf5 : wf ∉ Q23 := hwfQ
  have hwf6 : wf ∉ B23 := hwfB'''
# witness simp for incompatible disjunct must use the witness facts for its class only
def wit_incompat_names(tag):
    return {'wa': ['hwa3', 'hwa4'], 'wb': ['hwb3', 'hwb4'], 'wc': ['hwc3', 'hwc4'],
            'wd': ['hwd5', 'hwd6'], 'we': ['hwe5', 'hwe6'], 'wf': ['hwf5', 'hwf6']}[tag]
def plan_lines2(plan, K, al):
    if plan[0] == 'prune': return prune_lines(plan[1])
    _, tag, sub = plan
    L = [f'rcases B1 {tag} with ' + ' | '.join('h' for _ in al)]
    for z in al:
        match = [pl for (zz, pl) in sub if zz == z]
        if not match:
            br = [f'simp [{", ".join(wit_incompat_names(tag))}] at h']
        else:
            K2 = dict(K); K2[tag] = z
            br = [f'obtain ⟨{", ".join(hn(tag, i) for i in range(1, 7))}⟩ := h'] + plan_lines2(match[0], K2, al)
        L += ['· ' + br[0]] + ['  ' + x for x in br[1:]]
    return L
def orient_text(n, ordl):
    return (f'def Orient{n} (Q12 B12 Q13 B13 Q23 B23 : Finset (Fin 5)) : Prop :=\n  ∀ m : Fin 5,\n    ' +
            ' ∨\n    '.join('(' + conj('m', z) + ')' for z in ordl))
HEAD = '''set_option maxHeartbeats 200000000 in
theorem lemB (Q12 B12 Q13 B13 Q23 B23 : Finset (Fin 5)) (p q s wa wb wc wd we wf : Fin 5)
    (hQB12 : ∀ m, m ∈ Q12 → m ∉ B12) (hQB13 : ∀ m, m ∈ Q13 → m ∉ B13)
    (hQB23 : ∀ m, m ∈ Q23 → m ∉ B23)
    (hpB : p ∉ B12) (hpQ : p ∉ Q12) (hqQ : q ∈ Q12) (hsB : s ∈ B12)
    (hwaQ : wa ∈ Q13) (hwbB : wb ∈ B13) (hwcB : wc ∉ B13) (hwcQ : wc ∉ Q13)
    (hwdQ : wd ∈ Q23) (hweB : we ∈ B23) (hwfB : wf ∉ B23) (hwfQ : wf ∉ Q23)
    (Hall : ∀ p q s : Fin 5, p ∉ B12 → p ∉ Q12 → q ∈ Q12 → s ∈ B12 →
'''
HEAD2 = '''    (Hall2 : ∀ p q s : Fin 5, p ∉ B13 → p ∉ Q13 → q ∈ Q13 → s ∈ B13 →
'''
out = []
out.append(orient_text(1, ORD1)); out.append(orient_text(2, ORD2))
stmt = (HEAD + '    ' + ' ∨\n    '.join(PARTS1) + ')\n' + HEAD2 + '    ' + ' ∨\n    '.join(PARTS2) + ') :\n' +
        '    Orient1 Q12 B12 Q13 B13 Q23 B23 ∨ Orient2 Q12 B12 Q13 B13 Q23 B23 := by\n')
body = [WITF.replace('\n  ', '\n')]
body = WITF.split('\n')
body = [x.strip() for x in body]
pat = '⟨ap13, ap23, aq13, aq23, as13, as23⟩'
body.append('rcases Hall p q s hpB hpQ hqQ hsB with ' + ' | '.join(pat for _ in NP))
stats = {'leafcases': 0, 'refuted': 0}
for ci, case in enumerate(CASES):
    al = allowed(case)
    atoms = {(v, k): f'a{v}{"13" if k == 1 else "23"}' for v in COLW for k in (1, 2)}
    L = case_facts(case, atoms) + b1_lines(case, al)
    pqs = {case['p'], case['q'], case['s']}
    if pqs <= O1 or pqs <= O2:
        stats['leafcases'] += 1
        ordl, side = (ORD1, 'Or.inl') if pqs <= O1 else (ORD2, 'Or.inr')
        L.append(f'refine {side} ?_')
        L.append('intro m')
        L.append('rcases B1 m with ' + ' | '.join('h' for _ in al))
        for z in al:
            if z in ordl:
                br = [f'exact {ornest(ordl.index(z), len(ordl), "h")}']
            else:
                K = dict(case); K['m'] = z
                plan = refute(K, al, 2)
                assert plan, (ci, z)
                br = [f'obtain ⟨{", ".join(hn("m", i) for i in range(1, 7))}⟩ := h'] + plan_lines2(plan, K, al)
            L += ['· ' + br[0]] + ['  ' + x for x in br[1:]]
    else:
        stats['refuted'] += 1
        plan = refute(dict(case), al, 2)
        assert plan, ci
        L += plan_lines2(plan, dict(case), al)
    body += ['· ' + L[0]] + ['  ' + x for x in L[1:]]
text = '\n\n'.join(out) + '\n\n' + stmt + '\n'.join('  ' + x for x in body) + '\n'
open('/home/kevxhk/work/L-gct-210/lean/zbf/r7_1.txt', 'w', encoding='utf-8').write('\n' + text)
print(stats, 'lines', text.count('\n'), 'bytes', len(text.encode()))
