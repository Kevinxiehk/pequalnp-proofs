# HANDOVER-stage2 (written 20:32-20:34, 23 Nov; role "stage2" of the L-gct-210 team; 8 rounds, the last one cut after 30 minutes)

Paths below are relative to the workspace root (here `/home/claude/work/L-gct-210/`, on the other machine `cloud/L-gct-210/`).
Main files: `NOTES-stage2.md` (about 1370 lines; RESULT-R8 ... RESULT blocks at the top, sections `1`-`7`, `R2-1` ... `R8-4`),
`COMPUTE-stage2.md` (tasks S1-S7 for the big machine), scripts in `stage2/`, saved candidates in `stage2/data/`.

## 1. Role and question

L-gct-210: does every linear space L of 5x5 complex matrices with perm(J + t) = 120 for all t in L ("level space") have dim <= 8?
A refutation is an explicit 9-dim level space. Equivalent (chief, R0): no 10-dim space L^ = CJ + L on which perm = 120 ell^5.
My role: the "stage 2" of the 9-dim case analysis: assume dim L = 9 and exclude configurations by row/column structure.
Notation: a_r = 5 - dim(row-r projection of L), b_c same for columns, kappa^r / kappa'^c the FK annihilators (sum 1) when a_r = 1,
L_r = L cap {row r = 0}, lambda_{rr'} = dim L cap {rows r, r' = 0} (>= 2 by chief's Lemma C), Z_i = single-row elements in row i,
z_i = dim Z_i. Regimes: GEN = all a_r = b_c = 1 and all annihilators zero-free; REG1 = all a_r = b_c = 1 (zeros allowed);
the regime "some a_r >= 2" belongs to reg2 (`NOTES-reg2.md`).
Where it stands: GEN is closed (theorem, verified). REG1 is NOT closed; it is reduced to a problem on 5-dim spaces of 4x5 matrices
("(Q-r)", section 3 below), with one surviving type (z_i = 3) and four unclosed side cases.

## 2. Results

### 2a. PROVED (hand proofs; "V" = re-derived by verify2, see NOTES-verify2.md; "-" = not verified by anyone else as far as I know)

| # | statement | where | V |
|---|-----------|-------|---|
| P1 | tau-coordinates; unified pair criterion (G); Triple Theorem T1/T2/T2''; no minimal Type I pair in GEN (GEN-2) | sections 2-5c, R2-3 | V |
| P2 | Exception triples impossible (R3-1); Lemmas Y3, Y5 for 2-row elements (R3-2); configuration (II) impossible in GEN (R3-3) | R3-1..R3-3 | V |
| P3 | **Lemma N2-GEN** (moment problem sum c_j lam_j^k = sigma^k, k = 1,2,3, with zero-free weights has no admissible solution) and **THEOREM GEN: no 9-dim level space in GEN** | R3-5 | V ("Theorem GEN stands") |
| P4 | REG1 dictionary (Z1)-(Z3): kappa^r_j = 0 <=> e_j in row projection; (Z2) all five column-deleted 4x4 permanents vanish identically on L_r; z_r <= 4 - e(L_r); each single-row element e_i w^T gives the relation 1_{rows != i} (x) w | R4-1, R6-5 | partly (chief RP9 = Z2) |
| P5 | Lemma N2-Z (moment problem with zero weights: only families (alpha1), (alpha2), both with dominoes); Theorem N2-Z'; Cases A/B of family (alpha) | R4-3, R4-4, R5-2 | V |
| P6 | **M\***: explicit 6-dim level space (survivor (alpha3)), hyperplane of W_7 = full free column + 3-dim strongly level | R4-4 | V (exact) |
| P7 | **Theorem FO-M\***: dim T_1(M*) = 8 for ALL parameters; so every level space containing M* has dim <= 7 | R5-1 | V |
| P8 | **(FO)**: L lies in T_1(M) := {t : <cof(J+m), t> = 0 for all m in M} for every M inside L. **Lemma FO2**: L is totally isotropic for q_m = D^2 perm(J+m) on T_1(M) (BILINEAR, not hermitian): dim L <= dim T_1 - ceil(rank/2) | R5-4, R5-5 | V |
| P9 | **(Q-r)**: for dim 9, a_r = 1, X = L_r is a 5-dim space of 4x5 matrices with (i) N(J'+xi) = 120, (ii) G_j(xi) = perm_4(xi without column j) = 0 for all j, (iii) all ROW projections <= 3. Column projections <= 3 except possibly one column c with kappa^r = e_c, kappa'^c = e_r (case B0) | R5-6, R6-1, R7-4 | V (verify2 found the column gap; statement here is the corrected one) |
| P10 | **Cross family** X(a,b): T_1 explicit (dim 10, row-r part 3-dim); dead for all a not in C1 (b = 0 included) by (FO-r); FO2 bound 7 for b != 0 | R6-2, R6-3, R7-1 | - |
| P11 | Lemma (lambda = 5): needs Phi in GL_5 with C(xi) Phi + Phi^T C(xi) = 0. (T2): second-order part of chief's (**), linear in T | R6-7 | - |
| P12 | **Lemma (FO-r)**: if the row-r projection of L is 4-dim then the row-r projection Omega(L_r) of T_1(L_r) is all of C^5 (every G_j(J'+xi) is a first-order variation D_{t'} N(J'+xi)). Same content as reg2's dim L <= dim L_r + dim Omega(L_r) - 1 | R7-1 | listed as verified in BRIEF UPDATE 9 |
| P13 | (2,4) family: cofactor formulas; Omega contains e_0 and 1; Case A (s = 0) has Omega = C^5 | R7-2, R8-2 | - (formulas machine-checked, r7_fk24_formula.py, deviation 4e-14) |
| P14 | z_i = 3 forces four minimal pairs lambda_{ri} = 2, L_r = X_{ri} + e_i Z_i, L_i a (5,1) space with defect line C m, Z_i = (1,m)^perp; for <m,m> != 0: z_k = 0 (k != i), L_i non-split; (FO-r) for row i: the defect function is a first-order variation; dim T_1(M_i) >= 10 | R7-3 | - |
| P15 | Case B (B1) of (2,4): complete parametrisation by (mu, maximal isotropic Y_0) and reduction of Omega to criterion [CRIT] on quadrics; hand proof "dim Omega = 3 iff n two-valued" in the split k = 3 stratum | R8-2 | - (validated on 47 members) |
| P16 | (B0a): Lemma B0-1 (all 3x3 subpermanents of the 4x4 block of x_0 vanish); the (2,4) family never has a 4-dim column projection | R8-3, R8-2(0) | - |
| P17 | Graded form of (FO-r): (FO-r)_j <=> exists theta_j with D_{theta_j} P_k = P_{k-1}(xi^(j)) on L_r, k = 1..4 | R8-1 | - (NOT machine-checked yet) |

### 2b. EXACT / MODULAR
- M* is level; certificate (s1)-(s4) for dim T_1(M*) = 8, parameter-free, rational arithmetic: `stage2/r5_FO_Mstar.py` [exact].
- Triple Theorem T1 and the cubic identities of T2'': rational/Gaussian arithmetic (`stage2/t3_triple_exact.py`, `t5_triple_all.py`,
  `t10_typeII_exact.py`, `t13_T2pp.py`; sections 4-5b) [exact].
- No modular Groebner verdict exists from me. Three Singular runs (Case B, existential ideal, mod 32003) timed out at 100 s: NO verdict.

### 2c. NUMERICAL (LM searches, every solution verified on fresh points; counts are small)
- Census of (Q-r) solutions, about 55 verified: general starts 6, (2,4) about 24, (3,3) 15, (1,5) 1, (4,2) 0. ALL are of
  Frobenius-Koenig block type (every element has a zero s x t block, s + t >= 6) or cross type. No non-block solution found.
- Tests on every saved solution (`stage2/r7_table.py`): all solutions with z, z' <= 2 are DEAD by (FO-r), FO2 or (T2).
  ALIVE: only X_{ri} + e_i Z_i with z_i = 3 (files r6_fk_33_1_6, 33_1_8, 33_2_4, 33_2_8 and the cross space with a in C1).
  None of 5 ALIVE spaces tested extends to an 8-dim level space (`stage2/r6_extend.py`).
- (2,4) Case A: FO2 bound 8. Case B (B1): dim Omega = 2 generically, 3 or 4 on special loci (R8-2), never 5 in 47 members.
- Generic non-diagonal N2 blocks: FO2 bound 7 (26 blocks). Planes of minimal pairs alone: FO2 bounds 10-12 (no kill).
- Sanity of the tools on the 7 known spaces (L080, ex1, ex2, ex3, fam2, fam.6+1.4i, K5 from `chief/core.py`): FO2 bound = dim L
  in all cases; (T2) and (FO-r) pass on true L_r.

### 2d. REFUTED / DEAD (do not retry)
- Any 9-dim level space in GEN (P3). Minimal Type I pairs in GEN, exception triples, configuration (II).
- Families (alpha1), (alpha2); M* inside a 9-dim (or 8-dim) level space (P7).
- The cross family X(a,b) with a not in C1 (P10).
- CLAIM WITHDRAWN (R5-2): "all N2 blocks with a two-row column lie in family (alpha)" was a numerical over-claim (a 7 equations /
  7 unknowns count allows isolated solutions).
- CLAIM CORRECTED (R8-2): "Omega = span(e_0,1) for all of Case B of (2,4)" is false on special loci (dim 3: A' = n^perp with n
  two-valued, mu = -1; dim 4: A' = span{(1,-1,0,0),(0,0,1,2)}, mu = -1). So "Case B is dead at first order" holds for these examples
  only through reg2's inequality (dim L <= 7 resp. 8), and in general is unproved.
- CLAIM CORRECTED (R7-4): "column projections of L_r are <= 3" has the exception (B0).
- Hermitian version of FO2 (T^* H T) is WRONG; the form is bilinear (T H T^T). `r4_weights.py` first version misclassified rank-one
  solutions as counterexamples to N2-GEN (tolerance); there is no counterexample.
- reg2: "(S6') dim Omega <= 3 without a full free row" is false (their M*(x,y)); first order alone cannot close a_r = 2.

## 3. OPEN, ranked by promise

**O1. z_i = 3 in REG1 (the only ALIVE type).** Statement: there is no 9-dim level L with all a = b = 1 and a 3-dim single-row space
Z_i. Equivalent form (P14): no 5-dim "flexible non-split (5,1) space" L_i with defect line C m whose defect function
xi -> <m', G(J'+xi)> is a first-order variation of N, together with four minimal pairs. For <m,m> != 0 use verifyfl's SPLIT/TC5 and
(SL_m) (`NOTES-verifyfl.md` round 5: SL3-RED, Props I-ALL / II-ALL); isotropic m is untouched.
Next step: write (FO-r) for row i on every hyperplane of Z_i (HYP) as an exact linear system on the (5,1) normal form of rows
(`NOTES-rows.md`), feed rows' (5,1) search output (COMPUTE-stage2 S6). Effort: 1-2 days; this is the real remaining case of REG1.

**O2. Turn the (Q-r) census into a theorem, family by family (my best idea).** The (2,4) case showed the pattern: a block family is an
explicit low-dimensional variety (for (B1): maximal isotropic subspaces of the split quadric p'^T (J-I) q' plus one scalar mu), X always
contains a single-column element zeta, all cofactors are affine along zeta, and Omega becomes the rank condition of a small parametric
matrix (20 x 10 for (B1)). Do the same for (3,3) (rows 1,2,3 supported in two columns; this family contains the ALIVE z = 3 spaces, so
the expected verdict is "Omega = C^5 and FO2 bound >= 9 iff z_i = 3"), for (2,4) Case A (Omega = C^5 always; prove FO2 bound <= 8: X =
C xi_d + 4-dim isotropic space of the rank-9 quadric p_0(a-b) + a^2 + <p',q'> on 9 variables), and for (2,4) (B2).
The structural statement to prove is then: "a 5-dim solution of (Q-r) with Omega = C^5 and FO2 bound >= 9 contains a 3-dim
single-row part or a 3-dim single-column part" (the column alternative is needed: X = C_0 + Y of R8-2 (7) is level with a full free
column and was never tested). Tools: R8-1 (K-spaces: theta_j in (tau_j/4 + K_1) cap (tau_j/3 + K_2) cap (tau_j/2 + K_3) cap
(tau_j + K_4)), R8-1(d). Effort: (2,4) complete 1 day with the 24-core machine (S3'); (3,3) 1-2 days.

**O3. Block type is forced?** "Every 5-dim space of 4x5 matrices with (ii) and row projections <= 3 that is level is of FK block type
or cross type." Only numerical (55 solutions). Non-block solutions of (ii) alone exist (rows (x,y,0,0,0), (-x,y,0,0,0) plus two rows
on the last three columns). Next: COMPUTE S1 (census at scale with calibration rates) and S2 (exact charts). Effort: machine-bound.

**O4. (B0a).** L = L_r + L^c with entry (r,c) = 0 on L: needs a (Q-r) solution with a 4-dim column projection; (2,4) type excluded
(P16). Next: COMPUTE S7 (census with the column forced, stratified by Lemma B0-1). Effort: half a day.

**O5. Minimal pairs with zeros in the annihilators (Types I, II, I_0), FO2 on L_r + L_r'.** No explicit candidates were built; needs
criterion (G) solved with zeros (COMPUTE S4, S5). Effort: 1 day. Lower promise: planes alone give FO2 bounds 10-12.

**O6. Regime a_r >= 2** (reg2): needs "(S6-FO2) every 6-dim 4x5 level space without a full free row has FO2 bound <= 8".

Smaller items: machine-check P17 (30 minutes: solve for theta_j numerically on the saved candidates and compare with
`r7_FOrow.py`); get P10, P11, P13-P16 verified by a second reader.

## 4. Pitfalls
- FO2 uses the BILINEAR restriction T H T^T. The hermitian one gives a wrong bound (5 < 7 on ex1).
- LM solutions must be re-verified on fresh sample points (45 points are too few for a quartic in 5 variables: spurious "solutions").
- Scripts `exec` each other's preambles; the preamble re-reads `sys.argv` and overwrites SEED/NTR/MAXIT. Reassign such variables AFTER
  the exec line. Splitting a file at `if __name__=='__main__':` fails for files that themselves contain that string in an exec line
  (r7_FOrow.py): r8_caseB.py defines the helpers inline for that reason.
- Scripts contain the absolute prefix `/home/claude/work/L-gct-210/stage2/` and read candidates from `/tmp/*.npy`; on another machine
  run `sed -i 's#/home/claude/work/L-gct-210/stage2/#<new>/stage2/#g; s#/tmp/r#<new>/stage2/data/r#g' stage2/*.py`
  (the 18 candidate arrays were copied to `stage2/data/`).
- Rank tolerances: near-degenerate members (e.g. n = (1,1,1,1.0001)) give wrong ranks; rank-one solutions of the moment problem
  converge slowly and look like counterexamples.
- scipy `least_squares(method='lm')` needs #residuals >= #variables (pad with zeros); `max_nfev` counts Jacobian evaluations.
- [CRIT] of R8-2 is valid only for s != 0 on Y_0 and a, b independent; at s = 0 (Case A) use the D_0 form.
- (Q-r)(iii) is proved for ROWS only. Any argument that uses "column projection <= 3" must exclude (B0) first.
- Numerical census statements are about a few dozen solutions; "all" in section 2c means "all found".

## 5. Files

Notes (`NOTES-stage2.md`): top = RESULT-R8, R7, ..., R2, RESULT (round 1). Sections: `1`-`7` round 1 (pair criterion, tau-coordinates,
Triple Theorem); `R2-1..R2-5` GEN; `R3-1..R3-5` N2-GEN and Theorem GEN; `R4-1..R4-6` REG1 dictionary, N2-Z, M*, first (FO);
`R5-1..R5-7` FO-M*, FO2, (Q-r); `R6-1..R6-8` FK families, cross family, census, (T2); `R7-1..R7-4` (FO-r), (2,4), z = 3, what
remains; `R8-1..R8-4` graded (FO-r), Case B parametrisation, (B0).

Scripts (all `python3 -I stage2/<name>`, numpy/scipy only; helper libraries `pairlib.py`, `exactla.py`):

| script | purpose | command / runtime (approximate) |
|--------|---------|------------------|
| `r5_FO2.py` | CORE: `cof55`, `hess`, `FO2(Mb, rg)` -> (dim T_1, rank, bound); prints sanity table on the 7 known spaces | no args, about 20 s |
| `r5_FO_Mstar.py` | exact certificate for Theorem FO-M* | no args, under 1 min |
| `r5_Lr.py` | (Q-r) residuals (`perm4`, `G`, `res`, `dimT1`), small LM census | `SEED NT MAXIT`, 1-2 min |
| `r6_census.py` | (Q-r) census with rows U_i V_i (row projections <= 3), fresh-point check, saves .npy | `SEED NTR MAXIT [DM]`, about 1 min per 4 trials |
| `r6_fk.py` | census inside a block family | `KIND(24/33/15/42) SEED NTR MAXIT`, 1-2 min |
| `r6_cross.py`, `r6_cross_b0.py` | cross family: `Xab`, hand formula `T1_hand`, ranks | no args, under 30 s |
| `r6_T2.py`, `r6_T2_sanity.py` | (T2) test `T2test(B, rg)` -> (dim solution space, distance of J') | under 1 min |
| `r6_extend.py` | LM search for level extensions of a saved X | `FILES D NTRIAL`, 2-3 min |
| `r7_FOrow.py` | Omega = row-r projection of T_1(X) for all saved candidates and cross spaces | no args, about 30 s |
| `r7_fk24_formula.py` | checks the (2,4) cofactor formulas | no args, seconds |
| `r7_table.py` | (FO-r), FO2, (T2) on all saved candidates: the DEAD/ALIVE table | no args, about 1 min |
| `r8_caseB.py`, `r8_caseB2.py` | Case B (B1): build X from (mu, A', omega); compare T_1 tool, D_0 form, [CRIT]; 47 members | `SEED`, 5 s / 15 s |
| `r8_gen.py` | Singular script for "Omega = C^5 in stratum S1/S2/S3" | `STRATUM PRIME NV > f.sing`; std did not finish in 100 s |
| `r3_N2*.py`, `r4_*.py` | moment problem, N2 blocks, M* (rounds 3-4); see the headers | seconds to 2 min |

Data: `stage2/data/*.npy`, arrays of shape (5,4,5) = bases of X (rows 1..4 of the 5x5 matrices, row 0 = r): r5_Lr3_1_{1,2},
r6_census_31_{1,5}, 32_4, 33_4 (general starts), r6_fk_15_2_0, r6_fk_33_{1_4,1_6,1_8,2_4,2_8,2_9}, r7_fk24_24_{1..4},
r7_cross_aC1. Known spaces: `chief/core.py`, dictionary `SP`.

## 6. Pending compute tasks (`COMPUTE-stage2.md`; none has a result yet; results directory had only LEAN-1, VF-A, VF-B at 20:06)

| task | question | decision rule |
|------|----------|---------------|
| S1 | (Q-r) census at scale, with planted-solution calibration rates | every solution of block/cross type and z, z' <= 2 => DEAD by the three tests: supports O3; any solution outside the list: examine by hand |
| S2 | non-block solutions of (i)-(iii): numerical repulsion + exact Gr(5,20) charts | unit ideal on all charts, >= 3 primes => block type is forced (O3) |
| S3' (replaces S3) | Case B (B1): is rank S = rank S_exy possible with a, b independent? | unit for all 3 charts x 6 minors x 3 primes => (B1) dead at first order; non-unit => new first-order survivor, run FO2. Calibration NV = 1 must be non-unit |
| S4 | minimal pairs with zeros via criterion (G) | explicit pairs => FO2 on L_r + L_r'; bound <= 8 kills the type |
| S5 | diagonal N2 blocks with a two-row column | solutions outside family (alpha) would reopen the claim withdrawn in R5-2 |
| S6 | z = 3 against rows' (5,1) searches | a non-split (5,1) space whose defect function is a first-order variation = candidate for O1; none = evidence for O1 |
| S7 | (B0a): (Q-r) solutions with a 4-dim column projection | none in >= 200 starts per stratum (with calibration) => (B0a) numerically empty |

Honest summary: one theorem that stands (GEN), a set of verified tools (FO, FO2, FO-M*, (FO-r)), and for REG1 a numerical picture
(only z_i = 3 survives) that is not a proof. The last round corrected one of my own numerical claims and closed nothing.
