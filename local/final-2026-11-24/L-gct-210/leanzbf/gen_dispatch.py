# gen_dispatch.py: for each canonical (monotone) class pattern P of the (r1,r2) pair, the finite lemma listing the
# (E1)-allowed class patterns of the (r1,r3) pair (all three values present; B13 = B12 or its complement). Proof by decide.
import itertools
pats = [(0, 0, 0, 1, 2), (0, 0, 1, 1, 2), (0, 1, 1, 1, 2), (0, 0, 1, 2, 2), (0, 1, 1, 2, 2), (0, 1, 2, 2, 2)]
out = []
for P in pats:
    allowed = []
    for w in itertools.product(range(3), repeat=5):
        if len(set(w)) < 3:
            continue
        same = all((w[m] == 2) == (P[m] == 2) for m in range(5))
        comp = all((w[m] == 2) == (P[m] != 2) for m in range(5))
        if same or comp:
            allowed.append(w)
    nm = 'f13_cases_' + ''.join(map(str, P))
    W = ['w%d' % m for m in range(5)]
    same = ' ∧ '.join('(%s = 2 ↔ (%d : Fin 3) = 2)' % (W[m], P[m]) for m in range(5))
    comp = ' ∧ '.join('(%s = 2 ↔ ¬ (%d : Fin 3) = 2)' % (W[m], P[m]) for m in range(5))
    has = lambda v: '(' + ' ∨ '.join('%s = %d' % (W[m], v) for m in range(5)) + ')'
    concl = ' ∨\n      '.join('(' + ' ∧ '.join('%s = %d' % (W[m], w[m]) for m in range(5)) + ')' for w in allowed)
    s = ('theorem %s (w0 w1 w2 w3 w4 : Fin 3)\n' % nm +
         '    (hE1 : (%s) ∨\n      (%s))\n' % (same, comp) +
         '    (h0 : %s) (h1 : %s) (h2 : %s) :\n' % (has(0), has(1), has(2)) +
         '    %s := by\n' % concl +
         '  rcases fin3_cases w0 with rfl | rfl | rfl <;> rcases fin3_cases w1 with rfl | rfl | rfl <;>\n'
         '    rcases fin3_cases w2 with rfl | rfl | rfl <;> rcases fin3_cases w3 with rfl | rfl | rfl <;>\n'
         '    rcases fin3_cases w4 with rfl | rfl | rfl <;> revert hE1 h0 h1 h2 <;> simp +decide\n')
    out.append(s)
    print(nm, len(allowed))
open('/home/kevxhk/work/L-gct-210/lean/zbf/r11_9.txt', 'w', encoding='utf-8').write('\n' + '\n'.join(out))
