# HANDOVER-rows — the defect inequality (DI_5) for L-gct-210   (written 20:33, 23 Nov; role "rows", rounds 1–6)

Paths are relative to this workspace (`cloud/L-gct-210/` on the fork branch `coord-L-gct-210`). My notes: `NOTES-rows.md`
(RESULT blocks of rounds 6..1 at the top, then sections D, S, D', DI, R3, R4, R5, R6). My code and data: `rows/`.

## 1. Role and question
L-gct-210: is every linear space L of complex 5x5 matrices with perm(J + t) = 120 on L ("level space") of dimension <= 8?
(Largest known: 7. No 8-dim level space is known.) My branch is the DEFECT NORMAL FORM. For a 4x5 matrix Y put
c(Y)_j := perm(J + Y without column j) − 24; a 4x5 space L' is level if sum_j c(Y)_j = 0 on L'; C(L') := span{c(Y)} (inside 1^perp of C^5),
e := dim C(L'); "(d,e) space" = d-dim 4x5 level space with defect dimension e; EXTREMAL = (e+3, e).
Lift: L' (rows != r) + e_r (x) (C(L') + C1)^perp is a 5x5 level space of dim d + 4 − e, and every level space with a deletable row
arises inside such a lift. **(DI_5): d <= e + 3**, i.e. no (5,1), (6,2), (7,3) space. It says "a level space with a deletable
line has dim <= 7"; stage2 (z = 3) and reg2 (a_r >= 2) reduce to it. Column n of L' is NEUTRAL if c(Y)_n = 0 on L'.
Notation used below: c(Y), s(Y) = column / row sums; V = 1^perp in C^4; K strongly level = c(Y) = 0 on K (then dim K <= 3, Lean-checked
Lemma SL); N = L' cap ker s; X_n = single-column elements in column n; U_i = single-row elements in row i; W = (C + C1)^perp.

## 2. Results
### PROVED (hand proofs; "V2" = re-derived by verify2, see NOTES-verify2.md)
| result | where | status |
|---|---|---|
| Defect construction (lift; converse; dim <= d + 4 − e) | sec. D | used and re-derived by stage2 (Z3), verifyfl |
| DI_3: 2 x q level space has dim <= e + 1; Lemma D (Rado): p x q space with sum_j prod_i (1+x_ij) = q has dim <= q − 1; DDI; deletion formulas I1–I3; Prop. O; Cor. H (single-row part <= e, two-row part <= e+1); Lemma B'; Lemma TC | sec. DI | V2 |
| Lemma SL_3: a 3x5 space all of whose 3x4 column deletions are level has dim <= 2 | R3.8 | V2 |
| Theorem FL2*: level L containing e_i(x)U + e_r(x)U', U cap U' = 0, has dim <= 10 − dim(U o U') | R3.9 | V2 |
| From checked L_gct_215: 3x5 level <= e+3; dim(L cap {row r = 0}) <= 7; (8,3),(8,4),(9,4) excluded | R3.1 | V2 |
| Hyperplane Lemma: if no (e'+4,e') for e' < e, every hyperplane of an (e+4,e) space is extremal with the SAME C | R4.1 | V2 |
| U_i in C, U_i perp U_k, u_i + u_k <= e+1; RS-HYP (generic hyperplane of a minimal (e+4,e) space is not fully row-split) | R4.2, R4.3 | V2 |
| Lifting Lemma; D-UP ((D)_d => (D)_{d+1}, so (D) <=> (D)_7); C-UP | R4.7 | V2 |
| Transposed defect construction for a neutral column: L' = (Q|x), dim L' <= dim Q + 3 − e^col(Q); padding lemma | R4.10 | V2 |
| Theorem NCOL-S: defect line Cm, <m,m> != 0, e_i m^T in L', m without zero entry => dim L' <= 3 | R4.14 | V2 |
| (F1) c^(i)(Y).u = 0, c^(i)(Y) o u in C; (F2) U_i o U_k in C; (FS-DEC); (F1^T) | R4.15 | V2 |
| Theorem DC: dim L' = rank c + rank s + dim L'_dc; NC'-DC slack identity dim L' = e + 3 + delta − s1 − s2 − s3 | R5.2 | not yet verified |
| (SC1): for x e_n^T in L': <x, s(Y) − y_n> = 0 and (<x,y_j>)_{j != n} in C cap e_n^perp | R5.6 | not yet verified |
| **Theorem NCOL-P3**: defect line Cm (any m), K in L' strongly level 3-dim, s(K) = V, K on columns a,b,c, some Z with s(Z) = 0, c(Z) != 0 => m_a m_b m_c = 0 | R5.9 (contains R5.7) | not yet verified |
| **Theorem P51**: m with 5 distinct entries: no (5,1) space containing such a K that is spanned by single-column elements or lives on two columns | R5.11 | not yet verified |
| (R-LAW) for kernels spanned by single-column elements: rows of every Z in N lie in C; Prop. NCOL2-P (needs hypothesis (G)) | R5.12, R5.13 | not yet verified |
| (NCOL_3) + (DI_4x4) + no (5,1) + no (6,2) => no (7,3)  [erratum: R5.3(b) omitted the last two hypotheses] | R5.3, R6.3 | erratum by verify2 |
| X4 reduces to strongly level PLANES (PL); row-wise form of "strongly level" | R6.1, R6.2 | not verified; (S4) formula unchecked |

### EXACT / MODULAR
* Exact (integer / rational arithmetic): free-line-free 7-dim level spaces L_m and the second-kind space (`rows/exact7.py`, `exact7b.py`);
  identities I1–I3 (`di_ident.py`); FL2 toolbox (`fl2_ident.py`).
* Modular: none of mine finished. The calibration A4 of R6-1 did not finish in 100 s here (Singular std; msolve with localisation).

### NUMERICAL (complex LM, `rows/clm.py`; "found" = residual < 1e-9, fresh-point check)
* Existence: (4,1), (5,2), (6,3) found often; (5,1): 0/52 unseeded + 0/38 seeded; (6,2): 0/37; (7,3): 0/24; no 7-dim 4x5 level space.
  With one neutral column: (5,1) 0/8 [(4,1) 5/11], (6,2) 0/15 [(5,2) 3/5], dim 7 0/25 [dim 6 7/29]; two neutral: dim 6 0/22 [dim 5 12/25].
* **(NCOL)**: every extremal space has a neutral column: 87/87 mine + 33/33 seven-dim spaces of other agents; (6,3) with defect space
  fixed generic 0/46 vs control 4/19; block pattern (3,2) 0/30.
* Double tower: L = Q + [column n: 3 − e^col(Q)] + [row r: 4 − e^row(Q)], dim Q = e^row(Q) + e^col(Q) in all extremal examples;
  Q (4x4) again has a deletable line (120/120).
* 4x4 (via zero-column padding): (5,1) 0/14 [(4,1) 9/17]; (6,2) 0/15 [(5,2) 2/10]; any 6-dim 4x4 level space 0/15.
* Principal census: in 90 of 95 extremal spaces ker c is a strongly level 3-space with s = V; it always lives on <= 3 columns
  (types by column ranks (1,1,1), (2,1), (3), (3,2), (2,2,1)); also 49/49 fresh strongly level 3-spaces, 128/128 with a forced zero column,
  169/169 strongly level planes with injective row sums.
* (R-LAW): rows of N lie in C in 90/90 principal extremal spaces. (LAW) C = sum U_i + two-column part: 68/68. All 28 principal (4,1) are split.
* Slack census: delta = 0 in 126 of 135 tower positions; delta > 0 always paid exactly by s3 or s1; s2 = 0 always.

### REFUTED / DEAD (do not retry)
* "Extremal spaces are fully row-split": false (15 of 68). "dim(L'/{y_a = y_b}) <= 1" (EQ induction): false on all (6,3) tested.
* "Column-centred 4x5 level spaces have dim <= 3": false (dim 4 exists). "dim L <= e_row(L) + e_col(L)": false (padded circ(1,i,−i,−1)).
* "Every 7-dim level space contains a full free line": false (L_m). Round-1 target (A) (degenerate 4x5 spaces <= 4): false.
* "A strongly level MATRIX has <= 3 nonzero columns": false (4 columns common; `rows/sle5_s1005.npy` has 5). The true statement is about planes.
* (PRIN) "extremal with rank c = e => ker c strongly level": false for `rows/clm_p4_d5_defect2_s9.npy`.
* Row-centred 4x4 space with one-dimensional defect has dim <= 3: false for two-column defect lines (1 hit of 34).
* Hypothesis (G) of R5.13 fails for all known defect planes. Black-box use of L_gct_214/216/217 does not give (DC-COST).

## 3. OPEN, ranked by promise
1. **(PL) / X4: a strongly level plane with injective row sums has <= 3 nonzero columns.** Makes NCOL-P3 unconditional for every (4,1)
   whose ker c is strongly level with s = V. Next step: run R6-1 (cases B, C) on the 24-core machine; by hand, use R6.2 (three columns:
   pairwise orthogonal + one cubic; four columns: Gram pattern g_12 = g_34 etc., all triple products 0, one quartic). Effort: minutes
   of machine time if the Groebner basis terminates; otherwise 1–2 days by hand.
2. **Principal (5,1), remaining strata.** After TC5, PR3 (verifyfl), VF-A [modular] and P51: (i) kernel type (2,2,1) (exact system X5);
   (ii) kernel types (1,1,1), (2,1), (3), (3,2) with m having one zero and a REPEATED nonzero entry, e.g. (1,2,−4,1,0), (1,1,−1,−1,0),
   (1,1,1,−3,0). Approach for (ii): in P51's proof the cubic c(X) no longer vanishes identically; for x in X_n it gives
   <x,E_2(a)> = −3 mu <x,E_3(a)> (mu = the repeated value) plus one more linear relation; add the second-order cross terms. Each stratum is
   a small exact ideal (N = a (x) m is rank one). Effort: hours.
3. **My best idea — principal normal form for all e.** With (PL) and (R-LAW) an extremal principal space is L' = K + N, K one of five explicit
   types on <= 3 columns, N an e-dim subspace of C^4 (x) C mapped isomorphically onto C by column sums. Prove (R-LAW) type by type (it is
   equivalent to sum_j w_j <z_j, h_j> = 0 for h in K, w in C^perp; for single-column kernels it is R5.12; for two-column kernels start from
   the identity <z_d + z_e + z_f, h_a o h'_b + h_b o h'_a> = 0 obtained from the K-K-Z part of the cubic). Then (NCOL_e) and the exclusion of
   (e+4,e) in the principal strata become finite lists of small ideals indexed by (kernel type, e): unknowns = parameters of K, a basis of C,
   and N inside C^4 (x) C. For e = 1 this is exactly how NCOL-P3 and P51 were found. Effort: days; high value because it covers 90 of 95
   known extremal spaces.
4. **Non-principal strata.** (4,1): column-centred spaces (two-column m: exist) and ker c strongly level of row-sum rank < 3 (zeros' types,
   missed by LM). verifyfl's (SL_m) and its typed systems [DC3], [T22], [T31] cover dim 4 column-centred spaces. For e >= 2 the five
   non-principal extremal examples (kc_chk.py lists them) are the models to understand first.
5. **(NC'_e) = (DC-COST): delta <= s1 + s2 + s3** (R5.2). Needs the classification of doubly centred 4x4 level spaces (X1, Walsh
   coordinates, <= 18 unknowns) and then "each doubly centred direction is paid". The 4x4 statement (DI_4x4) (X3) is a sub-case.
6. **(NCOL_2), (NCOL_3) outside the principal normal form**: only (FS-DEC) (e = 3 row-carried defect: block sizes (4,1) or (3,2), X2) and R5.13.
7. **(D)_7**: every 7-dim level space has a deletable line (then (D) holds in all dimensions by D-UP). Only numerics (H5).

## 4. Pitfalls
* LM solutions on singular components are accurate only to ~1e-7 as subspaces: ranks decided at 1e-5 produce artefacts ("e^col = 4",
  "no deletable line", spurious single-row elements). Re-polish or use absolute thresholds; treat (n1, n2) column counts at 1e-3 / 1e-8.
* `clm.Problem` samples N = 140 points: too few for d >= 7 (COMPUTE-ERRATA A5). My d = 7 negatives stay valid (fewer constraints), hits would not.
* LM misses non-generic components (zeros' strongly level spaces of row-sum rank 1): a negative is evidence only with a positive control of the same kind.
* All pairings are BILINEAR (no conjugation); numpy SVD null vectors must be conjugated (`vh[r:].conj()`).
* "Principal" in my notes = ker c is a strongly level 3-space with s = V (then (DI_5) is automatic); verifyfl's "principal (5,1)" = ker c
  CONTAINS such a space. P51 is about the latter.
* `seeded.py` overwrites `seed_dD_eE_tT.npy`; `build7.build` mishandles e = 0; scripts insert an absolute `sys.path` (run without `-I` elsewhere).
* Unit ideal mod p is evidence, not proof; use >= 3 primes, coordinate charts and a non-unit calibration. One chart suffices in R6-1 because
  row permutations act on Walsh coordinates by signed permutations.
* STATUS time stamps in NOTES-rows.md are a few minutes ahead of the real clock in places. 

## 5. Files
Notes: `NOTES-rows.md` — D (defect construction), DI (round 2), R3, R4 (R4.1 hyperplane, R4.7 lifting, R4.8 NCOL, R4.10 transposed, R4.14–15),
R5 (R5.2 DC, R5.6 SC1, R5.9 NCOL-P3, R5.11 P51, R5.12 R-LAW), R6. Compute requests: `COMPUTE-rows.md`.
Scripts in `rows/` (numpy only; 2–8 s per LM start on one core):
* `clm.py` solver (modes level / deg / defect); `run_clm.py p d mode e s0 s1 tmax`; `seeded.py 'PAT' e_old d e ntrials tmax`.
* Searches: `nc_search.py d k s0 s1 tmax` (k neutral columns); `ncdef_search.py d e k s0 s1 tmax`; `fixC_search.py d e s0 s1 tmax [1|b32]`;
  `q44_search.py d e s0 s1 tmax [save] [cc]` (4x4 via padding); `cc_search.py`; `sle_chk.py d s0 s1 tmax`, `sl3col_chk.py`, `sl44_chk.py` (strongly level).
* Checks on saved spaces (`'PATTERN'` arguments, seconds each): `ext_chk.py` (neutral columns, deletable rows), `ncol_ext.py` (7-dim 5x5 spaces),
  `q44_chk.py` (tower laws), `slack_chk.py`, `kc_chk.py` (principal?), `tower_chk.py`, `rlaw_chk.py`, `sc1_chk.py`, `uiuk_chk.py`,
  `ncol1_chk.py`, `ncolp_chk.py`, `ncolp3_chk.py`, `sym_chk.py`, `r4_census.py`.
* Exact: `exact7.py`, `exact7b.py`, `di_ident.py`, `fl2_ident.py`. Groebner generator: `gb/x4gen.py P CASE OUT [CHART]`.
Data in `rows/`: extremal spaces `clm_p4_d{4,5,6}_defect{1,2,3}_s*.npy`, `seed_d*_e*_t*.npy`, `c52_*.npy`, `nc_d*_k*_s*.npy`, `ncdef_*.npy`;
4x4: `q44*_d*_e*_s*.npy`; strongly level: `sl3_s*.npy`, `sle_d{1,2}_s*.npy`, `sle5_s1005.npy`; column-centred: `cc_d*_s*.npy`.

## 6. Pending compute tasks (full specs in COMPUTE-rows.md)
| task | what | decision rule |
|---|---|---|
| R6-1 (first) | strongly level planes: cases B (4 columns), C (5 columns); calibrations A4, B3 must be non-unit | B and C unit at >= 3 primes => (PL) [modular] => NCOL-P3 unconditional for principal (4,1). Non-unit => send a point: new kind of plane |
| X5 | principal (5,1), kernel type (2,2,1) | unit => that stratum is empty |
| X4 | original 3-dim formulation (36 unknowns) | superseded by R6-1 |
| X1 | all doubly centred 4x4 level spaces of dim 1, 2, 3 (Walsh, Gr(k,9)) | list of components; input for (DC-COST) |
| X2 | (6,3) with one row carrying C = V_{012} + V_{34} | non-unit => (NCOL_3) false; unit => (NCOL_3) for row-carried defect |
| X3 | row-centred 4-dim 4x4 space with defect line not two-column | unit => no 4x4 (5,1) => step towards (DI_4x4) |
| H1 | LM: (5,1), (6,2), (7,3), unseeded / neutral column / seeded, >= 20 000 starts, raise N for d = 7 | any oracle-confirmed hit refutes (DI_5) and gives an 8-dim level space |
| H2, H3, H3b | census of 6-/7-dim 4x5 spaces; (NCOL), tower laws, (R-LAW) on fresh extremal spaces | one confirmed violation refutes the law; send the file |
| H4 | 4x4: (5,1), (6,2), any dim 6 | hit refutes (DI_4x4) |
| H5 | 7- and 8-dim 5x5 level spaces; deletable lines | a 7-dim space without deletable line refutes (D)_7 |
