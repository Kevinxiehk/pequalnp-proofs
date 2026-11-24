import sys

p = sys.argv[1]
s = open(p, encoding='utf-8').read()
missing = []


def rep(old, new):
    global s
    if s.count(old) < 1:
        missing.append(old[:80])
        return
    s = s.replace(old, new, 1)


rep("## THEOREM NCOL-S (a), (b), the TC5 NORMAL FORM (DI5.2), LEMMA QB, R4.2 (a), (b).   Not done: TC5 itself, PS, PR3, FL2*, R4.2 (c),(d), R4.3.",
    "## THEOREM NCOL-S (a), (b), the TC5 NORMAL FORM (DI5.2) and LEMMA Z (Z1, first part), LEMMA QB, R4.2 (a), (b), (c), R4.15 (F1), (F2), and the\n"
    "## NEW 4x5 analogue FL45 of Theorem FL (level 4x5 space with a full free row has dim <= 6).\n"
    "## Not done: TC5 itself (DI5.3), TS, PS, PR3, FL2*, R4.2 (d), R4.3.")
rep("verifyfl's DI5.1 / DI5.2 / R3.1 / R3.2 / R3.3 / R4.1(QB)).",
    "rows' R4.2(c) / R4.15(F1,F2), verifyfl's DI5.1 / DI5.2 / R3.1 / R3.2 / R3.3 / R4.1(QB)).")
rep("single_row_defC (rowE) [r4.part: see STATUS for whether it is in the current snapshot] |",
    "single_row_defC (rowE) |")

anchor = "\n### Dictionary / API guide"
new_rows = (
    "| rows' R4.2 (c) | single_row_t3 | Lev45 K, three distinct rows i, k, l with e_i u^T, e_k u'^T, e_l u''^T in K -> sum_j u_j u'_j u''_j = 0 |\n"
    "| NEW: Theorem FL for 4x5 level spaces | FL45 (zrow, one_add_zrow, FL45_core) | Lev45 K and e_i w^T in K for all sum-zero w -> finrank K <= 6. "
    "Core: for Y in K the matrix 1 + Y with row i replaced by ones has all five P4 equal and (5 + row-i sum) * P4_0 = 120, so the image of K under "
    "zrow i (zero out row i) is strongly level with a zero row, finrank <= 2 by LemmaSL3; the kernel is F_i, finrank 4 |\n"
    "| rows' R4.15 (F1), (F2) | Di_mem, R415_F1, R415_F2 | Lev45 K, e_i u^T in K, Y in K: D_i(Y)u = (P4 b (repl i u (1 + Y)))_b lies in defC K and has "
    "sum 0; (F1) the vector (tau(column b of Y without row i) * u_b)_b lies in defC K and sums to 0; (F2) e_k u'^T in K, k != i -> (u'_b u_b)_b in defC K |\n"
    "| glue between the three level notions | SLev_Lev45, DefLine_Lev45, SLev_DefLine | SLev K -> Lev45 K; DefLine K m and sum m = 0 -> Lev45 K; "
    "SLev K -> DefLine K m for every m |\n"
    "| NCOL-S corollary (a neutral column exists) | NCOL_S_neutral | hypotheses of SPLIT and 4 <= finrank K -> exists n, m n = 0 |\n"
    "| verifyfl's Lemma Z (Z1), first part | LemmaZ1 (zE, pc_ones) | DefLine K (e_0 - e_1) and z(e_0 - e_1)^T in K -> e2 z = 0, "
    "e2 z = (tau(z)^2 - <z,z>)/2 (Q = 0 on zeta) |\n"
)
i = s.find(anchor)
if i < 0:
    missing.append('anchor')
else:
    s = s[:i] + "\n" + new_rows.rstrip("\n") + s[i:]

rep(" - verifyfl's Theorem TC5 (DI5.3: Lemmas Z, LAG, NB and branches P1-P4), Theorem TS, Theorem PS / PR-RED / PR3 (R4.3-R4.5), round-5 items;\n"
    "   rows' FL2* (R3.9), R4.2 (c), (d), R4.3; the degree-wise conditions (C2'), (C3'), (C4') of DI5.2; the native 3x5 statement of SL_3.",
    " - verifyfl's Theorem TC5 (DI5.3: Lemma Z beyond the first part of (Z1), Lemmas LAG, NB, branches P1-P4 incl. the simplified (c3)),\n"
    "   Theorem TS, Theorem PS / PR-RED / PR3 (R4.3-R4.5), round-5 items; rows' FL2* (R3.9), R4.2 (d), R4.3, R4.15 beyond (F1), (F2);\n"
    "   the degree-wise conditions (C2'), (C3'), (C4') of DI5.2; the native 3x5 statement of SL_3.")
rep("LemmaQB; for FL2* the pieces P4_repl2, kc1_formula (= Delta_1 u), LemmaSL3, single_row_perp.",
    "LemmaQB; for FL2* the pieces P4_repl2, kc1_formula (= Delta_1 u), LemmaSL3, single_row_perp, single_row_t3, FL45, Di_mem, R415_F1/F2;\n"
    "   for TC5 the normal form TC5_normal with TC5_dd and LemmaZ1 (pattern: evaluate the normal form on z(e_0-e_1)^T and on Y + t z(e_0-e_1)^T).")
rep("x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 [r4] (.part) v.tail > FL.lean",
    "x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1 (.part) v.tail > FL.lean")
rep("z1 FS; z2 TC5 normal form; q1 QB; r4 Lev45_quad + R4.2 (a), (b); v.tail final theorem.)",
    "z1 FS; z2 TC5 normal form; q1 QB; r4 Lev45_quad + R4.2 (a), (b); r5 R4.2 (c); f1 FL45; g1 R4.15 (F1), (F2); h1 glue lemmas,\n"
    "   NCOL_S_neutral, Lemma Z1; v.tail final theorem.)")
rep("  v27 (QB); later ones in the STATUS lines.",
    "  v27 (QB), v28 (Lev45_quad, R4.2 a, b), v29 (R4.2 c), v30 (FL45), v31 (R4.15 F1, F2), v32 (glue, NCOL_S_neutral, Lemma Z1) = FL.lean.")
open(p, 'w', encoding='utf-8').write(s)
print('missing:', missing)
