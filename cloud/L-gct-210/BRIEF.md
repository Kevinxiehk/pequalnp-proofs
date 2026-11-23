# Team brief: gap L-gct-210 (hard, finite, either answer wanted)

You are one of several agents on ONE gap of the public pequalnp-proofs project (each gap is a
Lean 4 statement that counts only when a proof checker accepts it). Record:
/home/claude/work/L-gct-210/gap.json (read it).

## The question
Statement: every linear subspace L of 5 x 5 complex matrices with
sum over permutations f of prod_i (1 + t(i, f i)) = 120 (= perm(J + t) = 5!) for all t in L
has dim L <= 8. "It may be false": a REFUTATION is an explicit level space of dimension 9.
The largest known has dimension 7 (checked: Outside/L_gct_189.lean, and the general 2n-3
construction L080 in Gct/Helpers/LevelLow.lean).

Facts (all easy or checked):
- Level <=> P_1 = ... = P_5 = 0 on L, where P_k(t) = sum of all k x k subpermanents of t
  (perm(J+t) = sum_k (5-k)! P_k(t)).
- Write t = alpha_i + beta_j + gamma (alpha, beta sum-zero vectors in C^5, gamma doubly centred
  (DC), dims 4 + 4 + 16; the constant part is killed by P_1 = 0). Then
  2 P_2 = -20 sum alpha^2 - 20 sum beta^2 + sum gamma^2, a nondegenerate quadratic form on the
  24-dim space, so dim L <= 12 from P_2 alone. On DC matrices: P_2 = p_2/2, P_3 = (2/3) p_3,
  P_4 = (3/2)p_4 - (3/4)(sum_i r_i^2 + sum_j c_j^2) + p_2^2/8 + (1/4) tr((t t^T)^2)
  (r_i, c_j = row/column sums of squares; p_k = sum of k-th powers of entries).
- Checked bounds: 3x3 level <= 3 (Gct/L094); 3x3 DC <= 1 (Outside/L_gct_109); 4x4 DC <= 3
  (Outside/L_gct_216, 1300 lines); 4x4 row-centred <= 5 (Outside/L_gct_217); reduction to DC
  losing 2n (Gct/L092: all level <= DC bound + 2n); block-diagonal gluing (Outside/L_gct_110);
  power-sum tools: Kneser (L065), iterated Fermat (L067: if p_2..p_k vanish then k*dim <= N),
  L061 (p_2 = p_3 = 0 gives dim <= N/3), T3 (L163); product-type bounds (L090, L_gct_111/114/123).
  The n = 4 full bound (<= 5, "L-gct-091") is NOT checked; its helpers exist (Gct/Helpers/LS4).
- Previous team work on the general-n version (L-gct-086) is in /home/claude/work/L-gct-086/
  (NOTES-*.md: literature, smallcases, proof, construct, infra). Read NOTES-infra.md and
  NOTES-smallcases.md first. Tools there: smallcases/level.py (fast P_k + gradients via Ryser,
  exact checker), smallcases/search.py and extend.py (Levenberg-Marquardt searches),
  infra/Kit.lean and infra/KitFermat.lean (compiling Lean kits), infra/strip.py.
  Known pitfalls: p_4 need not vanish on DC level spaces (glue the 4x4 circulant line of
  L_gct_193); unstructured random search at n = 5 failed even to find dimension 7, so seed
  searches with known spaces; at n = 4 numerics suggest max level dim 5 and max DC dim 2.
- Evidence so far suggests the true maximum at n = 5 is 7 = 2n - 3 (so <= 8 has slack 1).

## Hard limits
- No heavy computation: no brute-force enumeration, no Groebner bases on large systems, no long
  solver runs; keep each run under ~3 minutes of CPU (2 cores shared by all agents). If a route
  clearly needs heavy computation, record that and drop it.
- Do not touch /home/claude/pequalnp-proofs (read only), no git, no contact with pequalnp.com.
  Python: python3 -I. Lean: compile only with
  /home/claude/tools/leancheck FILE /home/claude/work/L-gct-210/gap.json (about 50 s per run;
  helper test files may use a placeholder theorem; only the final file must state the gap).
- Final Lean file (if ever): imports only `import Mathlib` and `import PEqualNP.Defs`; checked
  lemmas from other files must be copied in; no comments, no double quotes, no # commands, no
  sorry/axiom/native_decide/instance/structure/attribute words; <= 512 KiB.

## Sharing
Work in /home/claude/work/L-gct-210/<role>/. Append concise findings to
/home/claude/work/L-gct-210/NOTES-<role>.md as you go; read the others' NOTES-*.md regularly.
Put a complete proof idea or a verified 9-dim space at the top of your notes under RESULT.
Check in by writing a line "STATUS <time>: ..." in your notes at least every 15 minutes.

## Report
When your budget ends (stated in your task) or you finish, reply with: what you established
(with evidence: exact or numerical), what you ruled out, and the best next step.

## UPDATE (round 2 state; read before anything else)
- Lean framework DONE: /home/claude/work/L-gct-210/lean/Frame210.lean (+ Frame210Fermat.lean), guide in
  NOTES-lean.md. It proves the d = 0 case and `gap_of_S_wlog`: the gap follows from r_A + d <= 4 under
  r_A <= r_B (r_A, r_B ranks of row-sum / column-sum maps on L, d = dim(L cap DC)). Also has polarization
  of P_3 (lev_T3), DC peeling, the P_3 coupling identity lev_P3_dc.
- Known 7-dim level spaces: L080, ex1, ex2, ex3, an exact 1-parameter family, a 4x2-block family (see
  NOTES-numerics.md, NOTES-split.md). None extends to 8 (first-order extension = L + one rank-one
  row/column-mean direction, which breaks P_2). No 8-dim level space found anywhere.
- KEY NEW LEAD (NOTES-lowd.md): numerically, P_2 = P_3 = 0 ALONE caps ANY subspace of the 24-dim
  sum-zero space at dim 7 (dim 8: 0 of 18 starts incl. seeded; dim 7: easy). Expected-dimension count
  for planes in V(quadric) ∩ V(cubic) in P^23 is negative from dim 8 on. So a sufficient (stronger)
  target is: NO 9-dim subspace of the sum-zero 5x5 matrices on which P_2 and P_3 both vanish.
  Exact formulas available: P_3 bidegree form and u = g - (3/2)a identities (NOTES-split.md),
  column-centred P_2..P_5 (NOTES-lowd.md), phi-identities (NOTES-methods.md), Hessian-image method
  (NOTES-dc5.md), stabilizer pattern of extremal examples (NOTES-dc5.md).
- Dead ends now: Fermat/Kneser directly (no commutative algebra structure; 45 coords give 15);
  naive growth Y4 >= 3d (fails on block-supported spaces); fixed-g relaxation alone (fails for
  block-supported g); small exact subsystems for d = 1.

## UPDATE 3 (supersedes the "KEY NEW LEAD" above)
- The P_2/P_3-only target is FALSE (NOTES-repr.md, exact): L9 = { x v^T + z e_4^T : x in C^5, sum z = 0 },
  v = (1, i, -1, -i, 0), is a 9-dim subspace with P_1 = P_2 = P_3 = 0 (not level: P_4, P_5 != 0).
  So any proof of the gap MUST use P_4 or P_5. Earlier LM "dim 8 impossible from P_2, P_3" was an artifact.
- Exact: the only level spaces containing the 3-row DC space K (dim 4) are K and five 5-dim extensions
  (NOTES-kbuild.md). Exact: a level space containing a full row/column block has r <= 7 (NOTES-hessmix.md).
- Special DC elements = singular points of perm_5; conjecture "Lemma Z": they have a zero row or column
  (NOTES-methods.md; agent lemmaz is on it).
- Growth data and product formulas: NOTES-growth.md (G1-G3 exact).
- LM negatives are unreliable at n = 5 unless the search passes a planted-solution calibration.

## UPDATE 4
- Theorem FL (NOTES-zeros.md; being independently verified by verifyfl): a level space containing a full free
  row or column has dim <= 7. Every known 7-dim space contains one.
- Observed law (NOTES-repr.md, 34 of 34 seven-dim spaces): exactly one row or column is "deletable"
  (zeroing it keeps the space level); equivalently y_c = 1 e_c^T - J/5 lies in the first-order extension
  space; this forces the column-mean coordinate beta_c = 0 on L. Conjecture (D): every level space of
  dim >= 7 has a deletable row or column. Exact identity (repr): perm(J + X V^T) = sum_a (5-|a|)! a! E_a(X) E_a(V).
- kbuild RESULT 2: local (single DC element, second order) mechanisms cannot bound the degenerate DC types.
- Lemma Z: ranks 1, 2 proved; ranks 3, 4 open; one-sided variant false (NOTES-lemmaz.md).

## UPDATE 5
- Theorem FL / Lemma SL are INDEPENDENTLY VERIFIED (NOTES-verifyfl.md: complete self-contained blueprint S0-S11):
  a level space containing a full free row/column has dim <= 7; a strongly level 4x5 space has dim <= 3.
- Shared checkout updated to the latest main project (c3037b0). Newly checked upstream: Outside/L_gct_214.lean
  (every 4x4 level space has dim <= 6), Gct/L218.lean. Read L_gct_214 if a 4x4 bound or its technique helps.
- chief final: ZBF tools, Lemma C, Theorem A, Theorem G, row-pair Types I, II, I' (NOTES-chief.md).
- rows: defect construction (NOTES-rows.md): deletable row r  <=>  L inside L' (+) e_r (x) (C(L') + C1)^perp.

## UPDATE 6 (state after cascade stages 2 and 3, round 1)
- stage2 (NOTES-stage2.md): chief's C4/C7 re-derived and correct; tau-coordinates; triple theorems T1, T2, T2'';
  Corollary S2: in the zero-free a = 1 regime a triple with X_ijk = 0 has exactly two minimal Type II pairs sharing
  a row. Open: minimal pairs themselves (Types I, II, I'), 21 Type-II/Type-II configurations, zero entries in
  annihilators, rows with a_r >= 2, pairs with lam >= 3.
- stage3 (NOTES-stage3.md): tools GZ, SR/SC, D2, D3, T1 (squarefree calculus), Q0, P2T; Theorem S3-A (ten B-type
  2-row elements are independent: a second 9-vs-10 pigeonhole); S3-B (conditional on HQ: single-row element);
  S3-D (minimal case forces block-type planes). Open statements O1-O5 (section 9).
- rows: (DI) proved for p = 3; working on the induction to p = 4, 5.

## UPDATE 7
- Newly checked upstream (shared checkout updated): Outside/L_gct_215.lean — a bound on the dimension of 4x5 level
  spaces (read its statement and proof technique: it concerns exactly the L' of rows' defect normal form), and
  Outside/L_gct_214.lean (4x4 level spaces have dim <= 6).
- stage2 round 2: Theorem GEN-2 (no triangular minimal pairs in the fully generic regime). stage3 round 2:
  Theorem N3' (lineality of perm_3 <= 3), MIN-A/B/C, configuration (II); round 3: (II) excluded under (NZ).
- verify2 has re-derived N3', N3'-L, R0, ZBF, ThB, LC, ThA with no error found so far.

## UPDATE 8 (17:40) — where everything now funnels
- THEOREM GEN is VERIFIED (NOTES-verify2.md, RESULT ROUND 2: full dependency list): no 9-dim level space has all
  a_r = b_c = 1 with zero-free row and column annihilators. Also verified: Theorem N1 (all a_r = 1, all lam = 3 =>
  single-row element), Lemma N2-GEN, R3-1 (exact), Lemma EQ, Theorem TC5 (no (5,1) space with defect line e_a - e_b).
- Lean (compiling): lean/zbf/Zbf.lean (R0, ZBF, UFD replacement, ThB, Lemma C general n, mixed coefficients);
  lean/fl/FL.lean (Theorem FL up to three remaining case lemmas HypS6-S8).
- THE CENTRAL OPEN STATEMENT is the defect problem: (DI_5) "a 4x5 level space L' has dim L' <= dim C(L') + 3".
  Since subspaces have smaller-or-equal defect and Lemma SL excludes (4,0), it suffices to exclude the pairs
  (dim, defect) = (5,1), (6,2), (7,3) ((8,4) is excluded by the checked upstream bound 4x5 level <= 7, L_gct_215).
  Known: (5,1) with two-column defect line is impossible (TC5). All 22 other known (4,1) spaces are "split"
  (contain e_i m^T). stage3 round 4: family N2 reduces (given the unproved (N2-unit)) to a transposed (5,1)/(6,1)
  space with an explicit defect line eta (NOTES-stage3.md sections 18-20).
- Still open besides (DI_5): (N2-unit); (S3) single-row element with z_r <= 2 when all a_r = 1; rows/columns with
  a_r >= 2 (Type I'); annihilators with zero entries (stage2 round 4 in progress); conjecture (D).
- New upstream (constructions/gluing only): Outside/L_gct_204 (block gluing, general), L_gct_206 (4x6 dim 7),
  L_gct_207 (5x7 dim 9).
