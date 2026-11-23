# HANDOVER-verifyfl.md  (written 2026-11-23 20:40 by agent "verifyfl"; workspace = cloud/L-gct-210/ on branch coord-L-gct-210)

## 1. Role and question
L-gct-210: every linear space L of 5x5 complex matrices with perm(J + t) = 120 on L has dim <= 8.  The team reduces it to the
DEFECT INEQUALITY (DI_5): a 4x5 "level" space L' whose deletion vectors C(Y) = (perm(J_4 + Y without column j))_j satisfy
C(Y) - 24*1 in C (dim C = e) has dim L' <= e + 3; to exclude: (dim, e) = (5,1), (6,2), (7,3).  My role: (i) independent verification of
Theorem FL / Lemma SL (e = 0; done, now Lean-checked), (ii) the case e = 1: no 5-dim space with defect line C m (m != 0, sum m = 0).
Everything is in NOTES-verifyfl.md (RESULT blocks at the top, newest first; sections BLUEPRINT, DI5, DI5-R3 ... DI5-R6, LOG).
Notation: V = sum-zero vectors of C^4, <x,y> bilinear, tau = coordinate sum, chi_a = (i^{ak})_k, zeta = (1,w,w^2,0), w = exp(2 pi i/3);
P = supp m, a column with m_n = 0 is NEUTRAL; kappa: column sums of Y are kappa(Y) m; s(Y) = row-sum vector; "column-centred" = kappa = 0;
"doubly centred" (DC) = also s = 0; isotropic m: <m,m> = 0; two-column m: |P| = 2.

## 2. Results
### PROVED (hand proofs in NOTES-verifyfl.md)                                             [status of independent check]
* Lemma SL (strongly level 4x5 space has dim <= 3), Theorem FL: BLUEPRINT S0-S11.          [Lean-checked, lean/fl/FL.lean]
* Lemma EQ, Theorem TC5 (no (5,1) for two-column m): DI5.                                  [verify2: verified]
* Theorem SPLIT (L' contains e_i m^T, <m,m> != 0 => dim <= 4), FS, TS, Lemma HYP: DI5-R3.   [verify2: verified]
* Lemma QB (quadratic normal form with defect), Theorem PS (principal stratum: L' = H (+) N, dim N <= 2), Lemma PR-RED,
  Theorem PR3 (no principal (5,1) for |P| = 3 non-isotropic): DI5-R4.                      [verify2: verified; PR3 also confirmed mod p, VF-B]
* (SL_m) reformulation: "column-centred with defect in C m => dim <= 3" for all non-two-column m implies no (5,1): R4.2.  [trivial]
* Round 5 (DI5-R5): Lemma C' (which blueprint lemmas survive), Lemma 3C (spaces supported on the 3 columns of P: dim <= 3, any m),
  Lemma NP (DC part on P: dim <= 2, types I' and the new type V; isotropic: <= 3), Lemma T (top-degree constraints), Props I', V,
  Theorem SL3-RED (|P| = 3, non-isotropic, dim K = 4 => one of the kinds (R1)-(R4) below): R5.1-R5.6.          [verify2: verified]
* Props I-ALL, II-ALL (blueprint type I / type II planes never lie in a 4-dim K when |P| = 3): R5.9.           [NOT yet checked by others]
* Pencil remark (|P| >= 4, four distinct nonzero entries, type (3,1): vartheta(Z_*) = 0, Theta(.,Z_*) = <phi,s>, phi isotropic): R5.7. [unchecked]
* Uniform target (SL_C) for e = 2, 3 (kernel of the column-sum map has dim >= dim L' - e): R5.10.                [one line, unchecked]
* R6.2/R6.3 (kind (R4): Z_0 is not chi_1 l^T; reduction of (R4) to a 2-dim classification).                    [unchecked]
### EXACT / MODULAR (Groebner)
* VF-A (other machine): for m = (1,w,w^2,0,0) the four explicit planes N(beta,xi) have NO one-vector extension: unit ideal at 4 primes
  [modular; generic affine normalisation - repeat on coordinate charts and over Q(theta)].  => no principal (5,1) for this m.
* VF-B calibration [modular]: N-problem for (1,2,-3,0,0) unit (= PR3); for (1,w,w^2,0,0) exactly the 24 row-permuted planes.
* Mine [modular, ONE prime 2147483629, msolve 0.10.1; verifyfl/exact/run/*.manifest]:
  - Lemma 3C as Gr(4,9): UNIT in all 126 cells, m = (1,2,-3,0,0) and (1,w,w^2,0,0); Gr(3,9) cell 0 non-unit (as required).
  - Lemma SL as structured [DC3]: UNIT in all 254 cases (pipeline calibration).
  - [DC3] for m = (1,2,-3,0,0): UNIT in 252 of 254 structured cases; the 2 generic rank-2 cells TIMED OUT (no verdict; files saved).
### NUMERICAL (floating point; reliability noted)
* New exact objects verified to 1e-12..1e-13: type V planes chi_1 (x) c+ (+) chi_3 (x) c- (every non-isotropic 3-support m);
  U_2 (x) (1/m) for isotropic m; K_2 = span(zeta (e_0-e_1)^T, zb e_2^T, zb e_3^T, h e_3^T), zb = conj(zeta), h = (1,1,1,-3): a 4-dim
  COLUMN-CENTRED space with defect exactly C(e_0 - e_1) (type (2,2)) - the two-column counterexample to (SL_m) in closed form.
* Climbs from the type II plane (calibrated: two-column control 3/3 reach dim 4): stop at dim <= 3 for (1,2,-3,0,0), (1,1,-2,0,0).
* All 35 known (4,1) spaces with good m are split with principal ker kappa; no column-centred (4,1) found for non-two-column m
  (but see pitfalls: the 4-dim Grassmannian searches have a control rate of only ~4%).
### REFUTED / DEAD (do not retry)
* (K4) "kappa != 0 => ker kappa strongly level": false (two-column third kind; isotropic m).  (Z1)-(Z3) "column-centred with defect line
  => strongly level" in dim 1-3: false (such spaces are plentiful, type (3,0)).  (SL_m) for two-column m: false (K_2).
* Isotropic split case via "m in two slots": only reproduces the linear conditions.  Lemma EQ over all column pairs: equivalent to the
  definition of the defect line.  Pencil counting alone cannot exclude type (3,1).  (B-i) of the blueprint fails with defect.
* Levenberg-Marquardt on Grassmannians of 4-dim spaces (typed or not): fails even on the control.  di_ext.ext can miss existing
  degenerate extensions (0/36 for chi_1 (x) Lam_M although chi_1 e_j^T extends it): its negatives count only with a same-kind control.
* msolve on the unstructured Gr(3,12) cells (27 unknowns, ~1 min each) or with the v(theta) parametrisation of isotropic lines: too slow;
  use the structured generator with the chart v = (1,a,b,-1-a-b).

## 3. OPEN, ranked by promise
STATE OF (5,1)  (K := ker kappa of a hypothetical (5,1) space is a 4-dim column-centred space with defect line C m, of type (q,d),
q = rank s|_K, d = dim of its DC part; "principal" = K contains a 3-dim H with s(H) = V and zero defect; it is a sub-case of (3,1)).

| stratum of m | split (e_i m^T in L') | principal K | K of type (0,4),(1,3) = [DC3] | K of type (2,2) = [T22] | K of type (3,1) = [T31] |
|---|---|---|---|---|---|
| two-column | PROVED (TC5, all cases) | PROVED | PROVED | PROVED | PROVED |
| |P|=3, non-isotropic, distinct entries, e.g. (1,2,-3,0,0) | PROVED (SPLIT) | PROVED (PR3; mod p VF-B) | (0,4) PROVED; (1,3) = (R4): modular 252/254, 2 generic cells pending | OPEN = (R3); sub-kinds "N contains a type I or II plane" PROVED (R5.9) | OPEN = (R1) (vartheta(Z_*) != 0); vartheta = 0 PROVED |
| |P|=3, two equal entries (1,1,-2,0,0) | PROVED (SPLIT) | PROVED (PR3) | as above, not yet run | as above | OPEN = (R1) and (R2) (Z_* = v (e_a - e_b)^T on the equal columns) |
| |P|=3 isotropic (1,w,w^2,0,0) | OPEN (SPLIT fails; rows R3.10) | MODULAR (VF-A) | OPEN (NP: dim N_P <= 3; 3C, T, I' hold) | OPEN | OPEN |
| |P|=4 | PROVED if <m,m> != 0 | rows P51 for distinct entries and kernel types (1,1,1),(2,1),(3),(3,2); N-problem VF-B running; rest OPEN | OPEN | OPEN | OPEN (pencil remark R5.7) |
| |P|=5 | PROVED if <m,m> != 0 | rows P51 (same types); rest OPEN | OPEN | OPEN | OPEN |
(rows' Theorems NCOL-P3 and P51: NOTES-rows.md R5.9, R5.11 - not checked by me.  Principal K for repeated entries / kernel type (2,2,1): open.)

Kinds left for |P| = 3 non-isotropic (Theorem SL3-RED; N_P := DC part supported on P has dim <= 1):
 (R1) type (3,1), N = C Z_*, Z_* on P with <z_a,z_a> != 0 (Z_* = v_+ c+^T + lam v_- c-^T, one-parameter family);
 (R2) type (3,1), m = (1,1,-2,0,0), Z_* = v (e_a - e_b)^T on the equal columns;
 (R3) type (2,2), S = u^perp (u isotropic), a neutral column active on N (N contains no type I/II plane);
 (R4) type (1,3), N 3-dim DC with both neutral columns active.

O1 (highest promise, hours): finish [DC3] = (R4) exactly.  (a) run the two saved cells (verifyfl/exact/run/*_ab_ab.ms) with more time/threads,
   then the 254 cases at 2 more primes, then m11m2, iso (expect possible NON-unit for iso), two.  (b) MY BEST IDEA: "Lemma A with defect" =
   classify ALL 2-dim DC spaces with defect in C m (gen_n1s.py, k = 2: <= 14 unknowns per case; decompose the non-unit cases with Singular
   minAssGTZ).  If the planes with exactly one neutral column active and dim N_P = 1 are only type I / type II planes, Props I-ALL / II-ALL
   kill (R4) at once (R6.3), independently of the slow cells; and the list is exactly the input needed for [T22].
O2 (days -> hours with the engine): [T22] and [T31].  Write gen_n3.py: for each component N of the k = 2 list (explicit, few parameters), unknown
   Y_1, Y_2 column-centred with s(Y_r) spanning a plane (if a neutral column is active on N the plane is u^perp, <u,u> = 0: use the chart
   u = (1,a,b,-1-a-b)); gauge: pivot coordinates of N zero.  Control: K_2 must be found for m = e_0 - e_1.  gen_n2.py: Z_* on P (6 coordinates,
   first-nonzero charts) plus Y_1, Y_2 (stage a), Y_3 (stage b) with prescribed row sums b_r; for |P| = 3 non-isotropic add the split
   "vartheta(Z_*) != 0" with the gauge <column j of Y_r, column j of Z_*> = 0 (j in P), which adds 3 linear equations per Y_r.  If the engine
   shows that the neutral columns of Y_r vanish, Lemma 3C finishes (R1).
O3 (hand, 1-2 days): (R3) = blueprint S7/S8 with the extra form; Lemma T-type "top-degree" coefficient extraction (Y + tZ, Z in N) is the tool
   that worked for types I, II (R5.9); needs the list of O1(b).  (R2): m = (1,1,-2,0,0); constraints from my round-5 working (the first pair is proved in R5.6 (ii); the others are derived from t^2-coefficients
   as in Lemma T but NOT yet verified numerically or written up):
   for all Y in K: <v, 2y_a - s> = <v, 2y_b - s> = 0, <v^2, y_n> = <v^2, y_n'> = <v^2, y_c> = 0, [v,v,y_n,y_n'] = 0.
O4 (after e = 1): (SL_C) for dim C = 2, 3 with the same three typed systems (COMPUTE-verifyfl.md N6); C containing a two-column vector must
   be treated separately (there (SL_C) is false).
O5: isotropic 3-support (split case and all types), |P| = 4, 5: no hand reduction yet beyond Lemma C', 3C, NP(b), T, I', the pencil remark;
   the unstructured gen_n1.py works for any m (220 cells of Gr(3,12), ~1 min per big cell): run [DC3] there first.

## 4. Pitfalls
* "Unit ideal mod p" is evidence, not proof (bad reduction); use >= 3 primes, coordinate charts instead of one generic affine equation, all
  cells, a calibration that must be NON-unit, then an exact run or a verified rational certificate (COMPUTE-verifyfl.md, RIGOUR NOTES).
* The ambient space A_m (column sums in C m) has dimension 16; older text says 17 (labels only).
* Numerics: see REFUTED/DEAD; LM tolerances produce artefacts near strongly level spaces (ranks at 1e-6 are unreliable for residual ~1e-9).
* m^perp is bilinear (no conjugation); for isotropic m, m lies in m^perp.  di_ext.mperp handles this; do not "fix" it.
* Theorem PS / PR3 need only an H with zero QUADRATIC defect and s(H) = V (the proof uses only the isometries B_j).
* Two-column m escapes everywhere through theta_3 (m_i + m_j) = 0 (R5.9 Step 0); any argument for (R3) must use a third nonzero entry.
* Scripts need `python3 -I` and add their own path; each numerical run was kept under 3 CPU-minutes; STATUS timestamps are +-5 min.
* In gen_n1s.py the legacy charts 'th'/'c3' are still accepted by build() but cases() uses 'ab','z1','z2'; do not mix manifests.

## 5. Files  (all under cloud/L-gct-210/)
* NOTES-verifyfl.md: RESULT ROUND 6..1 (top), BLUEPRINT (S0-S11), DI5 (EQ, TC5), DI5-R3 (SPLIT, FS, TS, HYP), DI5-R4 (QB, PS, PR3, SL_m),
  DI5-R5 (C', 3C, NP, T, I', V, SL3-RED, I-ALL, II-ALL, strata status, exact programme), DI5-R6, LOG.
* COMPUTE-verifyfl.md: requests A-F, NEXT N1-N6, rigour notes (self-contained definitions in section 0).
* verifyfl/exact/: exactlib.py, gen_n1.py, gen_n1s.py, test_gens.py, test_gens2.py, README.md (commands, states), run/ (manifests, 4 .ms files).
  Substitution tests: `python3 -I test_gens.py`, `python3 -I test_gens2.py` (2 s each, no engine).  Runtime per case: see README.
* verifyfl/ (numerics, numpy): core.py (perm, sl_check), di_core.py (Cvec, defect, onb, kernel_of), di_ext.py (mperp, res_m, ambient_m, ext,
  chk_m), r3_z.py / r5_dc.py / r5_r3.py (Grassmannian LM searches - unreliable for dim 4), r4_pr3.py (planes N, formula of PR3),
  r4_n2.py (N-problem), r5_checks.py (type V, U_2 (x) 1/m, 3C identity), r5_lemT.py, r5_propII.py (coefficient identities),
  r5_climb_r2.py / r5_climb_r3.py (climbs; the latter is the calibrated one), r5_types.py (census).  Each runs in < 2 min: `python3 -I file.py`
  (some take arguments: see their docstrings).  Data: verifyfl/*.npy (r5_r2_control_zeta_1.npy = K_2 numerically; r4_n2_inj_2_*.npy).
* Other agents: NOTES-rows.md (defect normal form, NCOL-P3, P51), NOTES-stage3.md, coord/local/results/VF-A, VF-B (exact results).

## 6. Pending compute tasks and decision rules
* verifyfl/exact/run/n1s_m12m3_p2147483629_k3_rho2_piv{0,1}_l0_ab_ab.ms: `msolve -g 2 -f F -o F.gb`.  Both [1] => [DC3] holds for
  m = (1,2,-3,0,0) modulo this prime, i.e. kinds (R4) and type (0,4) are empty there; a non-unit basis => a 3-dim DC space with defect:
  extract a point and test whether it extends (it would be new).  Then repeat all 254 cases at 2147483497 and 2147483077.
* COMPUTE-verifyfl.md A: redo on coordinate charts and exactly over Q(theta) (decides: no principal (5,1) for (1,w,w^2,0,0)).
* B (running elsewhere): N-problem, |P| = 4, 5: unit => no principal (5,1) for that m; (1,2,-4,1,0) expected non-empty, then test extensions
  EXACTLY (my numerical "no extension" there is weak).
* NEXT N1 (k = 2 classification; k = 3 emptiness), N2 [T31], N3 [T22], N4 cross-checks (3C and SL done at one prime here), N5 other supports
  and symbolic m, N6 (SL_C).  Rule: [DC3], [T22], [T31] all unit for m  <=>  (SL_m)  =>  no (5,1) with defect line C m.
* C, D, F2 (numerical Grassmannian searches): low value (see pitfalls); prefer exact ideals and climbs from explicit seeds (di_ext.ext with
  a same-kind positive control, e.g. r5_climb_r3.py).
