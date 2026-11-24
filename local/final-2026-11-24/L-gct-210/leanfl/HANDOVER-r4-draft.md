# HANDOVER-leanfl (L-gct-210, role leanfl) -- written 2026-11-23 ~20:10 UTC (machine clock) at the end of round 4

Gap: every linear space L of 5x5 complex matrices with perm(J + t) = 120 on L ("level space") has dim <= 8.
leanfl turns the FL strand (Lemma SL, Theorem FL, the defect normal forms of rows / verifyfl) into compiling Lean 4.
Everything lives in ONE self-contained file built from part files in lean/fl/ (imports Mathlib and PEqualNP.Defs only).

## 1. Build, compile, guard

  cd /home/kevxhk/work/L-gct-210/lean/fl
  PARTS="pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1 ps ps2 ps3 ps4 ps5"
  (for p in $PARTS; do cat $p.part; done; cat w.tail) > FLl.lean
  /home/kevxhk/work/tools/leancheck FLl.lean        (one machine-wide Lean slot; ~207 s and 8.4 GB on an idle machine,
                                                     far slower under load; leancheck kills a compile after 25 min)
- Helpers: namespace PEqualNP.Outside.L_gct_210_aux.FL (opened in pre.part, closed in w.tail), `open Finset`, `noncomputable section`.
- w.tail = final theorem `PEqualNP.Outside.L_gct_210` (placeholder statement: Lemma SL /\ Theorem FL row /\ Theorem FL column).
  v.tail is the OLD tail (name ..._fl) which the project guard refuses: at the top level only `theorem PEqualNP.Outside.L_gct_210` may stand.
- Guard rules (all checked by leancheck + `node .../outside-guard.mjs imports FILE imports.json lean/PEqualNP/Outside/L_gct_210.lean`):
  no line beginning (after spaces) with add_; no comments, quotes, #, sorry/axiom/native_decide/instance/structure/attribute/...;
  the words Lean, IO, Meta, FS, System, Elab ... are refused as whole identifiers; 512 KiB cap (waived by Kevin for now).
- Quick tests: a small file = pre a b c + new part + test.tail (closes the section and namespace) compiles in a fraction of the time.
  Lemmas that need LemmaQB take the hypothesis `QBc K m` (ps.part) so that they can be tested this way; QBc_of (ps2) discharges it.

## 2. What is proved (see NOTES-leanfl.md RESULT block for the full table up to v31 = h1.part)
Rounds 1-3: Lemma SL, Theorem FL (row, column), Lemma DS, defect construction (Prop. D, R1), Lemma EQ, Theorem SPLIT (two forms),
Theorem FS, Lemma HYP, Hyperplane Lemma, Lemma SL_3 (zero-row form), NCOL-S (a), (b), TC5 normal form, Lemma QB, R4.2 (a)-(c),
FL45, R4.15 (F1), (F2), SLev_Lev45, DefLine_Lev45, NCOL_S_neutral, LemmaZ1.
Round 4 (this round):
- ps.part: QBc (QB (b) as a hypothesis), phi_onto (finrank (H.map rs) = 3 for strongly level H => rs and every phi_j map H onto V),
  pol_alg / PS_pol (polarised QB between Y in H and Z in ker s), PS_f (the linear form is <f, s(.)>, f in V explicit),
  PS_nf = verifyfl THEOREM PS (a): z_j = (kappa m_j / 4) 1 + m_j phi_j(Y_f) with Y_f in H (rows: z_j^0 = m_j B_j f with B_j = -phi_j o s^-1);
  np3_col, np3_X, np3_alg (Gram certificate: C.E = 2 nu (a-b-c)(a-b+c)(a+b-c)), NCOL_P3_core.
- ps2.part: QBc_of, ThmPS_a, NCOL_P3 (rows THEOREM NCOL-P3, three-column case, H vanishing on columns 3, 4: m_0 m_1 m_2 = 0).
- ps3.part: rs_cperm, DefLine_perm, NCOL_P3_perm (any three active columns sigma 0, 1, 2 for a column permutation sigma).
- ps4.part: sq_prop (m_j^2 X = lam m_j, sum m = 0, m != 0 => X = 0), ThmPS_b (<f,f> = 3 kappa^2 / 4 in this normalisation).
- ps5.part: PS_c_key, ThmPS_c (verifyfl PS (c): principal stratum => finrank K <= 5; via N0 = N cap {col sum j0 = 0}: its column
  j0 image is totally isotropic (Q1), the column map is injective on N0, so dim N0 <= 1, dim N <= 2, dim K <= 3 + 2).
COMPILE STATUS of ps..ps5: see the last STATUS line of NOTES-leanfl.md.

## 3. Next targets (verified by verify2; ledger NOTES-verify2.md ROUND 5/6)
- PR-RED (R4.4) and THEOREM PR3 (R4.5): the PS normal form is now available; PR3 needs Z_* = chi_1 l^T (isotropic columns, Newton),
  chi_2-coordinates (Ps4 / Qv tools exist), the cubic C_n(Y) - 24 formula and a rank-3 quadratic form.
- rows NCOL-P3 two-column / one-column cases (B_b = -B_a: eigenvalue argument), NCOL-P (R5.7), SC1 (R5.6: column analogue of R415_F1;
  needs additivity of P4 in a column, i.e. a pc-multilinearity lemma), P51 (R5.11), NCOL2-P (R5.13).
