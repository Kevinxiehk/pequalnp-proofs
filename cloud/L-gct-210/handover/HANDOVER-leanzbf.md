# HANDOVER-leanzbf (L-gct-210, role leanzbf) -- written 2026-11-23 20:40, for an agent starting cold

Gap: every linear space L of 5x5 complex matrices with perm(J + t) = 120 on L ("level space") has dim <= 8.
My job was to turn the team's hand proofs into compiling Lean 4. Everything below is in ONE self-contained file
(imports `Mathlib` and `PEqualNP.Defs` only). Paths are relative to this workspace (here /home/claude/work/L-gct-210/,
on the other machine cloud/L-gct-210/ on branch coord-L-gct-210).

## 1. How to compile; which file is the base for which

CURRENT FILE: `lean/zbf/R3e.lean` (identical snapshot `lean/zbf/R3e_ok.lean`): 5914 lines, 290,918 bytes, 340 declarations.
Last check (20:24): lean exit code 0; axioms [propext, Classical.choice, Quot.sound]; guard 0 / 0; format counts all 0.
Compile: from the project's `lean/` directory (Mathlib cache built), `lake env lean /path/to/R3e.lean`. To see the axioms,
append `#print axioms PEqualNP.Outside.L_gct_210_zbf` to a COPY (the file itself must not contain `#`). Here I used the
wrapper `/home/claude/tools/leancheck FILE gap.json`, which does exactly that and prints the guard and format counts.
Time: 50 s to 2.5 min wall per run on the shared machine (about 45-50 s CPU, single thread). Memory was not measured.
"statement verbatim: False" from the wrapper is expected: the final theorem is a placeholder, not the gap statement.

Chain of files (each = previous + text inserted before the `end <namespace>` line; all compile):
  Zbf.lean (round 1, 2015 lines) -> Zbf2 -> Zbf3 (N3') -> Zbf4 (C4) -> Zbf5..Zbf10 (C7) -> Zbf11.lean (round 2 final, 5227 lines)
  -> R3a.lean (Zbf11 with namespace renamed + `add_` fix; no new maths) -> R3b (column versions, normal forms)
  -> R3c (T0, algebraic cores, S2 count) -> R3d (S2, S2*) -> R3e (T1 identity) = CURRENT.
Namespace: `PEqualNP.Outside.L_gct_210_aux.ZBF` (`open Finset`). Final theorem (last in file):
`PEqualNP.Outside.L_gct_210_zbf` = R0 + Lemma C (rows, columns) + N3' + C4, each in definition-light form.
`lean/zbf/FrameZbf2.lean` = Frame210 kit + the Zbf11 namespace (OLD namespace names, not guard-compliant; compiles).

## 2. What is proved (Lean name -- informal statement -- paper source). No sorry, no axiom anywhere.

Notation: `pm u` = permanent of u : Fin n x Fin n -> C; `blk rho kappa u` = permanent of the block (rows rho, cols kappa);
`Lev n L` = level space; L^ = CJ + L is modelled by pairs w = (c, t), `hat n w = c + t`, ell(w) = `w.1`;
`rowMap r`, `colMap c` (line projections); `rowsZero L r r'`, `colsZero`, `rowsZeroS L S` (Finset of rows), `cellsZero L K`;
`blockSpace L r c` = U for a zero block (r c : alpha + beta = Fin n; rows inl x cols inr vanish); `dotL kappa z = sum z_m kappa_m`.

Layer A -- foundations (chief sec. 2-3; verify2 round 1)
- lev_scale, lev_scale_emb (R0: pm(c + t) = n! c^n); lev_line, lev_FK, lev_FK_row, lev_FK_block (no zero row/block at ell != 0).
- perm_zero_block, pm_zero_block, pm_zero_block_sets (ZBF: permanent factors over a zero block).
- poly_const_of_mul, line_const, ufd_unit, ufd_zero (elementary replacement of the UFD step, by restriction to lines).
- zbf_prod, zbf_ufd, zbf_zero, zbf_lineality, zbf_witness('), zbf_cases (the ZBF dichotomy: either blk_1 = k ell^|a|,
  blk_2 = k' ell^|b|, k k' = n!, or ell = 0 on U and one block permanent vanishes on U).
- thB_quad, thB_ker, thB_img, thB_dim, thB_cases, thB_pair, thB_img_or, thB_Bx, q0_isotropic_bound (Theorem B).
- lemmaC_gen / lemmaC / lemmaC_col_gen / lemmaC_col / lemmaC_nine (Lemma C in the verifier's general form:
  dim L <= dim(L cap {two rows = 0}) + 2n-3, any level space; n = m+2).
- pm_laplace_row, pm_laplace_two, ca2, ca2_full, ca2_col (zeros' CA2 by direct Laplace), thA, thA_col (Theorem A),
  single_row_SR (stage3 SR), lev_tr (transposition), lev_mix, lev_mix_hat, lev_rows (mixed coefficients).
- n3 (3x3 level => dim <= 3; chief N3), row_proj_le, rows_pigeon, one_not_mem_row, row_onto (row_e(L^) = C^n when a_e = 1).
- The same chain at an ARBITRARY base point b: BLev, blev_of_lev, blev_of_const, zbf_prodB, zbf_ufdB, thB_*B,
  lemmaC_genB, lemmaC_col_genB, blev_line, blev_mix, blev_rows.

Layer B -- N3' (stage3 sec. 10; verify2 round 1)
- n3prime: pm b != 0, pm(b + eta) = pm b on V0 (3x3) => finrank V0 <= 3. n3prime_weak (<= 4, short).
- n3prime_L_full: Corollary N3'-L (any n, any 3x3 block with ell(u0) = 1).
  Lean route differs from the paper: Lemma C at base point b + explicit algebra (Bad, bad_X4c/X3c/X1c, n3alg) with
  machine-generated certificates (lean/zbf/py/gen_alg.py, gen_n3p.py).

Layer C -- pigeonhole and Theorem G pieces (stage3 sec. 16; chief ThG)
- rows_submodular, cells_submodular, rows_rank, cells_rank (P); rows_disjoint_bound, rows_inj_bound (G1);
  dS, dS_submodular, stage3_G2 (G2).
- pm_mask_sum, pm_mask_zero, pm_mask_factor, thG_term, thG_masked (generalised Laplace identity of ThG);
  perp_bound, rank_one_bound (A, B in C^N with a.b = f(a) g(b) on A x B => dim A + dim B <= N + 1).

Layer D -- C4 (chief sec. 4; stage2 sec. 1)
- c4: Lev 5 L, pair (r, r.succAbove p) with finrank L = finrank X + 7 and both row ranks = 4 => every 3x3 subpermanent
  `Bx r p x j0 q0` of every x in X_{rr'} vanishes. Valid for every dim L. c4_col: column version (R3b).
  Proof is NEW and shorter than the paper's (ZBF witness + ThA kernels; helpers thA5, c4_left, c4_right, c4_cols).

Layer E -- C7 / C7'' (chief sec. 4, RP5; stage2 sec. 1-3; verify2 3a)
- c7_pair_thB (ThB for a column pair), c7_tau, c7_pair_x (pair criterion (a), (b), (d) of C7' by test vectors),
  c7_sep, c7_types (plane combinatorics, any index type), c7_lift (I^ = ker of two independent relations; dimension count),
  c7_hI, fk_annihilator, second_relation, dot_zero_of_row, c7_rows, c7_rows_full, c7_rows_ind.
- c7_final: minimal pair with row ranks >= 4 => annihilator data kappa, kappa', nu, nu' exist and, if kappa, kappa' are
  zero-free, the points (rho, rho') are of Type I or II (two points on an anti-diagonal, or plus one corner with
  omega^2 = -c^2, sigma_corner^2 = -sigma^2). Defs TypeCl, MinPairCl, MinPairNF package this.
- c7_final_cl (rows), c7_final_col (columns by transposition; rowsZero_tr, map_tr_row, tr_min).
- c7_nf, minPair_nf, c7_rows_nf, c7_cols_nf: NORMAL FORM in tau-coordinates (stage2 sec. 3): for all t in L,
  sum_{m in Q_b} kappa_m t(r,m) + sum_{m in Q_a} kappa'_m t(r',m) = 0, Q_a = {rho' = rho'_a}, Q_b = {rho = rho_b}.

Layer F -- triples (stage2 sec. 4, 5, 5b; verify2 3b)
- t0: T0 for a row triple x column triple (Fin 3 + Fin 2 block).
- t2_cubic, t2_core: the T2 cubic 2t(t a1 + a1 a2 + a1 a3 - a2 a3); a linear form whose kernel lies in its zero set has
  no a1, a2, a3 coefficient. t2pp_cubic, t2pp_core: the T2'' cubic contains no hyperplane (any j != 1).
- t1p_alg: T1' -- the six equations of the cyclic Type II triple have no solution (any i with i^2 = -1).
- rowsZeroS_single(_finrank), s2_count: X_123 = 0 and dim L_i = 5 force (2,2,2) or (2,2,3) up to order.
- ZF, PairI, PairII, pair_I_or_II; s2_core, s2 (Corollary S2), s2_star (S2*).
  EXPLICIT HYPOTHESES (precise Props, NOT proved): `T1Hyp` (three ZF rows, all pairs minimal => X_123 != 0; the 3,108-
  configuration exact check), `T2Hyp`, `T2ppHyp` (hand proofs; only their algebraic cores above are formalized),
  `R31Hyp` (exception triples, the 1,800-configuration check). s2 takes T1Hyp, T2Hyp, T2ppHyp; s2_star also R31Hyp.

Layer G -- stage 3 start (stage3 sec. 7)
- blk_row_scale; t1_identity: CA2 => identity (T1), for ANY row set S not containing e: x in L supported on rows S,
  xi in L with row e = 0, a_e = 1 => every 4x4 subpermanent of (rows of x on S, rows of xi elsewhere; row e deleted) is 0.

Findings for the paper authors: no step failed. C7'' needs exactly the corrected form of (d) (omega_j + omega_l = 0 AND
sigma_j = sigma_l); condition (c) and "at most two points per anti-diagonal" are not needed. C4 needs no classification
of C = a b^T + b a^T. T1' holds for both signs of i.

## 3. Guard and format status (R3e.lean)

- guard: lines starting with `add_` = 0; namespaces outside PEqualNP.Outside.L_gct_210 = 0; final theorem is last.
  (Structure fields `add_mem'` are written `carrier := {...}; add_mem' := by` on one line. Never start a line with
  `add_zero`, `add_comm`, ... inside a wrapped `rw [...]`.)
- format: no comments, no double quotes, no `#`, no sorry / axiom / native_decide, none of the words instance, structure,
  inductive, macro, syntax, notation, elab, initialize, attribute. `def`, `noncomputable def`, `abbrev` are fine.
- Size 291 KB < 512 KiB, but the cap was declared suspended; the file is not the gap proof anyway.
- Sanity: appending a deliberately false lemma yields exactly one error and exit 1 (lean/zbf/sanity.log, on Zbf10).

## 4. Next targets, in order, with sources and working tricks

1. Finish Theorem G (chief lines 27-35, 119-126). I had the full plan but did NOT write it: index type
   `abbrev IdxG n m := {A : Finset (Fin n) // A.card = m} x {T // T.card = m}` (card = C(n,m)^2 by Fintype.card_prod,
   Fintype.card_finset_len); vectors vecA v (A,T) = pm (maskAT A T (if row in A then v else 1)), vecB u likewise with
   roles swapped; `mask_prod`: vecA * vecB = pm(mask(mix v u)) * (m! (n-m)!) via thG_term with Z = T^c and
   Fintype.equivOfCardEq (cards from Fintype.card_coe, Fintype.card_of_subtype (p := ...), Fintype.card_subtype_compl),
   plus a lemma blk of all-ones = (card)!; pairing = thG_masked after Fintype.sum_prod_type and Finset.sum_subtype;
   then a Fintype-indexed copy of perp_bound / rank_one_bound with hypothesis "f a = 0 -> a perp B" and spans handled by
   Submodule.span_le into kernels. Result: rho_m + rho_(n-m) <= C(n,m)^2 + 1. dim K_2 >= 5 is further work.
2. T2 and T2'' in full (stage2 sec. 4, 5b): missing is the structural part -- I_3 = row-triple image + C(1,1,1) has
   dim = dim L + 1 - dim X_123 (copy the I0 computation of c7_lift with `(rowMap r1).prod ((rowMap r2).prod (rowMap r3))`),
   I_3^perp = N_12 + N_13 + C n**, C12 = C13 up to complement, the kernel K_S, then t2_core / t2pp_core finish.
   Then T1Hyp / R31Hyp by certificates (stage2 t5_triple_all.py, t10_typeII_exact.py; verify2 r3_exact*.py).
3. GEN-2 (stage2 R2-3) and its inputs SR (have single_row_SR), S2-d / GEN-tri, GEN-0, GEN-lin.
4. Stage 3 (sec. 7, 11-16): facts (i), (ii) of the squarefree calculus, Lemma T, MIN-A (rank-16 as hypothesis or
   certificate, stage3/span16_exact.py), TV, MIN-B, plane lemmas, Theorem N1. Work with subpermanents directly
   (`blk`); "P_a P_b P_c P_d = 0 in A_4" = all 4x4 subpermanents vanish. t1_identity applied to xi_1 + xi_2 gives
   Q_x R_c R_d = 0 without polarisation.
5. Normalisations of Type I / II (c = 1/(K_1 - K_2), sigma_0, y = (-1 + eps i)/2) from the sum conditions in c7_final.

Tricks that worked
- Build a new file by inserting text before the `end` line with a small script; compile once per batch; snapshot.
- `linear_combination` with hand or script certificates; check them first with exact Fractions treating every symbol
  (including i, with hi : i*i = -1 as a hypothesis with a coefficient) as independent (py/chk_t1p.py is a template).
- "Hyperplane inside a cubic" statements: instantiate the hypothesis at explicit test points scaled to avoid division
  (e.g. (b2 T, b2 A1, -(aT + b1 A1 + b3 A3), b2 A3)), then `linear_combination`; no irreducibility theory.
- Dimension counts: `rank_nullity L f`, `finrank_sup_vec W v (h : v not in W)`, `Submodule.finrank_mono`, then `omega`.
  Name big submodules as opaque variables: `obtain ⟨I0, hI0⟩ : ∃ I0, I0 = ... := ⟨_, rfl⟩`.
- Existence of annihilating functionals: `Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance`; convert a
  functional to a dot product with `dual_eq_dotL` (uses `pi_eq_sum_univ'`).
- Polynomial-in-s arguments: `polyLine_blk` + `poly_zero_of_ne` (vanishing for all s != 0 => identically 0);
  top coefficient via row scaling `blk_row_scale` (see t1_identity).
- Fin 3 / Fin 5 facts: `revert ...; decide`; `rcases fin3_cases a with rfl | rfl | rfl`; permanents: `permanent_two`,
  `permanent_three` with `simp only [pm, permanent_three, Matrix.of_apply, vec3_0, vec3_1, vec3_2]; ring`.
- Transposition: `lev_tr`, `trE`, `rowsZero_tr`, `map_tr_row`, `tr_min`, `blk_tr`, `Submodule.mem_map_of_mem`.
- Classical sets in statements: quantify over explicit `Finset`s with membership-iff hypotheses; use `classical`
  inside proofs (there is no DecidableEq on C in scope for `if rho m = ...`).

Traps
- `omega` can fail to identify two finrank terms that print identically (one from `rank_nullity`, one from a
  hypothesis; instance paths differ). Fix: `have e : <explicit statement> := rank_nullity L f`, then `clear` the raw one.
- `lemmaC_gen (m := 3)` etc. produce `Fin (3 + 2)`; give the `have` an explicit `Fin 5` type before `omega`.
- `rw` cannot unify higher-order patterns such as `fun p => ?d p.1 * ?w p`: instantiate the lemma with explicit
  arguments and use `exact h.trans (...)`.
- `rw [<- h0]` with h0 : ... = 0 rewrites every 0; use `rw [..., add_zero, ...] at h0; exact h0` instead.
- A `by simp` argument inside `rw [lemma (fun x => by simp)]` runs before unification; pass implicit args (`p := ...`).
- `subst h` with h : a = b eliminates b (replaces it by a); state the equation in the direction you want.
- Renamed Mathlib lemmas: `Polynomial.eval_finsetSum`, `Polynomial.finsetSum_coeff`; `div_mul_cancel₀ a (h : b ≠ 0)`.
- sympy is not installed; plain Python with Fractions (`python3 -I`).

## 5. File map

- lean/zbf/R3e.lean, R3e_ok.lean -- CURRENT (see sec. 1). R3a..R3d(.lean, _ok.lean) -- earlier round-3 states.
- lean/zbf/r3_1.txt .. r3_4.txt -- the round-3 text blocks (R3b = R3a + r3_1, R3c = R3b + r3_2, R3d + r3_3, R3e + r3_4).
- lean/zbf/Zbf.lean, Zbf2.lean .. Zbf11.lean, Zbf*_v*_ok.lean -- rounds 1-2 states (old namespace PEqualNP.Gct.ZBF210).
- lean/zbf/part2a..part2e.txt, part3a.txt, part3b.txt, part4.txt .. part10.txt -- round-2 text blocks.
- lean/zbf/FrameZbf.lean, FrameZbf2.lean -- Frame210 kit + ZBF namespace (round 1 / Zbf11), for use with the P_k tools.
- lean/zbf/py/gen_n3.py, gen_alg.py, gen_n3p.py (certificate generators for N3 / N3'), chk_t1p.py (T1' certificates).
- lean/zbf/*.log -- checker logs (r3a..r3e.log, z11.log, frame2.log, sanity.log).
- NOTES-leanzbf.md -- RESULT tables and API guides of rounds 1-2 (top), full STATUS log, round-3 STATUS lines at the end.
- Mathematics: NOTES-chief.md (sec. 2-4), NOTES-stage2.md, NOTES-stage3.md, NOTES-verify2.md (verifier's repairs).
