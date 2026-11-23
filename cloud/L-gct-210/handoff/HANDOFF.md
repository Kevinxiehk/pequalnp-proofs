# L-gct-210 handoff: cloud session → local 24-core session

> **ERRATA (20:14, read first):** see `COMPUTE-ERRATA.md` next to the COMPUTE files. In particular: no 8-dim level space is
> known (calibrate at dim 7); the statement "(S6′) dim Ω ≤ 2 without a full free row" used below under "Blocked 4" and C2 is
> FALSE — the target is (S6-FO2): no full free row ⟹ FO2 bound ≤ 8; C1 acceptance is d − e ≥ 4; every numerical hit needs a
> fresh-point test and `oracle.py`; unit ideals mod p are evidence, not proof.


Written 2026-11-23 19:40 (Europe/Berlin). Everything referred to below is in the bundle
`L-gct-210-bundle.tar.gz` (unpack anywhere; paths below are relative to its `L-gct-210/` folder).

Statement: every linear space L of 5×5 complex matrices with perm(J + t) = 120 on L ("level space")
has dim L ≤ 8. Conjectured truth: the maximum is 7 = 2n − 3.

## 0. Lease and submission notes

- You hold the desk lease, which is why the desk stopped offering this step to the cloud session.
  Keep renewing it; a lease is capped at 6 hours ("release it and ask again"). The cloud session has
  stopped polling the desk.
- No pull request adds `lean/PEqualNP/Outside/L_gct_210.lean` so far (checked every ~10 min until 19:25).
- Thanks for the check-mode finding: a 9-dim space could only justify `statement_seems_false`.
- A final proof file must be ≤ 512 KiB and import only Mathlib and PEqualNP.Defs. Our helper files
  already total more than that (section 3), so a complete proof would need heavy compression.
  Upstream's `L_gct_215.lean` (4×5 level ≤ 7) is 7,559 lines, for scale.

## 1. Where the proof stands

### Approach
1. **Reformulation (R0).** L is level ⟺ perm = 120·ℓ⁵ on L̂ = ℂJ ⊕ L, with ℓ(cJ + t) = c.
2. **Zero-block factorisation (ZBF).** If u ∈ L̂ vanishes on S×Z with |S| + |Z| = 5, then
   perm(u) = perm(u[S,Zᶜ])·perm(u[Sᶜ,Z]); on linear families each factor is a power of ℓ or one factor
   vanishes. This is how P₄, P₅ enter. (P₂, P₃ alone cannot work: `NOTES-repr.md` has an exact 9-dim
   space {x vᵀ + z e₄ᵀ : Σz = 0}, v = (1, i, −1, −i, 0), with P₁ = P₂ = P₃ = 0.)
3. **Row invariants.** For a row r: a_r = 5 − dim(row-r projection of L) ≥ 1, L_r = L ∩ {row r = 0}
   (a 4×5 level space of dim 4 + a_r when dim L = 9), λ_{rr'} = dim(L ∩ {rows r, r' = 0}).
4. **Defect normal form** (`NOTES-rows.md`, section D). For a 4×5 matrix Y let
   c(Y)_j = perm(J₄ + Y minus column j) − 24 and C(L') = span{c(Y) : Y ∈ L'}, e = dim C(L').
   Then L' ⊕ e_r ⊗ (C(L') + ℂ1)^⊥ is a 5×5 level space of dim (dim L') + 4 − e; conversely every level
   space with a "deletable" row r (zeroing row r keeps it level) sits inside such a space.
   `handoff/oracle.py` implements and tests this (all known (3,0), (4,1), (5,2), (6,3) spaces lift to
   7-dim level spaces, error ≤ 1e-12).

### Proved
Hand proofs re-derived by an independent verifier (`NOTES-verify2.md`); **[Lean]** = also compiles in Lean.
- R0, ZBF, Theorem B (2×3 zero blocks), Lemma C: for every level space and every row pair,
  dim(L ∩ {rows r, r' = 0}) ≥ dim L − 7 (general n: 2n − 3), CA2, Theorem A, 3×3 level ≤ 3,
  Theorem N3′ (if perm(b) ≠ 0 and perm(b + η) = perm(b) on a linear space V₀ of 3×3 matrices then
  dim V₀ ≤ 3), C4. **[Lean: lean/zbf/Zbf*.lean]**
- **Theorem FL / Lemma SL.** A 4×5 space with c(Y) = 0 on it ("strongly level") has dim ≤ 3; a 5×5 level
  space containing a full free row {e_r wᵀ : Σw = 0} or column has dim ≤ 7.
  **[Lean: lean/fl/FL.lean, 4,928 lines, no hypotheses]**
- **Theorem GEN.** No 9-dim level space has all a_r = b_c = 1 with zero-free Frobenius–König annihilators
  (`NOTES-verify2.md`, RESULT ROUND 2, full dependency list; one link is an exact computation over ℚ(i)
  on 1,800 configurations).
- **Theorem N.** dim L = 9, all a_r = 1, all λ_{rr'} ≥ 3 ⟹ L contains a single-row element.
- Defect inequality pieces ((d,e) = a d-dim 4×5 level space with dim C = e). Target (DI₅): d ≤ e + 3.
  It suffices to exclude (5,1), (6,2), (7,3); (4,0) is Lemma SL and (8,4) is upstream L_gct_215.
  Proved: no (5,1) with defect line ℂ(e_a − e_b) (TC5); no (5,1) containing e_i mᵀ with ⟨m,m⟩ ≠ 0
  (SPLIT); one row carrying a nondegenerate defect space ⟹ d ≤ e + 3 (FS); (DI) for 2-row spaces;
  a 3×5 space with all 3×4 column deletions level has dim ≤ 2 (SL₃).
- Tools: for M ⊆ L level, L ⊆ T₁(M) = {t : D_t perm(J + m) = 0 ∀ m ∈ M} and L is totally isotropic
  there for q_m = D² perm(J + m) (FO / FO2, `NOTES-stage2.md` R4-6, R5).

### Blocked (four open branches)
1. **Defect inequality.** (5,1) for isotropic-split and non-split defect lines; sufficient statement
   (SL_m): "a 4×5 space with all column sums zero and c(Y) ∈ ℂm has dim ≤ 3 for m not of the form
   e_a − e_b" (`NOTES-verifyfl.md` R4.2). Then (6,2), (7,3): reduced to "every extremal (e+3, e) space
   has a neutral column" (true on 120 of 120 examples) plus a 4×4 defect problem (`NOTES-rows.md` R4).
2. **Single-row elements** (all a_r = 1, no minimal row pair): generic case done; a 2-dim single-row
   part and a few patterns open (`NOTES-stage3.md`, RESULT ROUND 6, section 25).
3. **Minimal row pairs with zeros in the annihilators** (`NOTES-stage2.md`, RESULT-R6).
4. **Some a_r ≥ 2** (L_r is a 4×5 level space of dim ≥ 6): closed if "a 6-dim 4×5 level space without a
   full free row has dim Ω ≤ 2" (`NOTES-reg2.md`); all 80 known 6-dim spaces are "free row ⊕ 2" or
   "one neutral column".

Evidence that nothing above 7 exists: every structured or seeded search for dimension 8 failed
(adversary, repr, numerics, rows). **Random-start LM is useless at n = 5**; it misses exact spaces that
exist. Every search must first pass a planted-solution calibration.

## 2. Computations to run (priority order)

Helpers are writing exact, self-contained specs for their own sub-problems as
`COMPUTE-<role>.md` (verifyfl, rows, stage3, reg2); they will be in the next bundle. The tasks below can
start now.

### C1. Decisive existence test: (5,1), (6,2), (7,3), and 7-dim 4×5 level spaces
*Why:* an 8-dim 5×5 level space with a deletable row exists ⟺ one of these exists. Half of the proof
strategy assumes they do not. A hit means the true maximum is 8 and the strategy must change.
- Unknowns: a d-dim subspace L' ⊆ ℂ^{4×5} (Grassmannian chart [I_d | X] after a random unitary change of
  basis of ℂ²⁰) and an e-dim subspace C ⊆ 1^⊥ ⊆ ℂ⁵ (chart for its annihilator).
- Equations: ⟨w, c(Y)⟩ = 0 for all Y ∈ L' and all w ∈ (C + ℂ1)^⊥, plus Σ_j c(Y)_j = 0. Each is a
  polynomial of degree ≤ 4 in the coordinates of Y; impose all coefficients, or sample ≥ 2× the number
  of monomials at fixed random points.
- Solver: holomorphic (complex) Gauss–Newton / LM with analytic Jacobian. `rows/clm.py` has a
  vectorised implementation (`solve`, mode 'defect'); validate any new solver against `handoff/oracle.py`.
- Calibration (must pass first, same code path): (4,1), (5,2), (6,3) from random starts (our rates:
  10/25, 3/21, 4/19 with the defect space fixed to a coordinate hyperplane ∩ 1^⊥).
- Runs: (5,1), (6,2), (7,3), and (7, any e) with 4×5 level only: ≥ 20,000 random starts each, plus
  seeded starts (known (d−1, e) and (d−1, e−1) spaces from `rows/*.npy` + one random direction).
- Accept a hit only if residual < 1e-12, the basis is well conditioned (σ_min/σ_max > 1e-3), and
  `oracle.py` reports the right (d,e) and a lift level error < 1e-10 at fresh points.
- Output: hit files (.npy), or the calibration and failure counts per case.

### C2. Census of 6-dim 4×5 level spaces (branch 4)
- System: 6-dim L' ⊆ ℂ^{4×5} with Σ_j c(Y)_j = 0 (P₁..P₄ of the 4×5 matrix vanish).
- Calibration: recover planted spaces from `rows/clm_p4_d6_defect3_*.npy` after perturbation, and find
  5-dim ones from random starts.
- Runs: ≥ 20,000 random starts on Gr(6,20); also Gr(7,20) (does any 7-dim 4×5 level space exist?).
- For each solution report: the dimension of each single-row part {w : e_i wᵀ ∈ L'}; neutral columns
  (columns n with C(L') ⊆ e_n^⊥); e; and, for L' placed in rows 0..3 of a 5×5 matrix, dim T₁(L') and
  the dimension of the row-4 projection Ω of T₁(L'). Decides: is every 6-dim space "full free row ⊕ 2"
  or "exactly one neutral column, Ω 2-dimensional"? Any other type is a candidate for a 9-dim space.

### C3. (SL_m) for sample lines m (branch 1)
- System: 4-dim K ⊆ {Y ∈ ℂ^{4×5} : all column sums 0} with c(Y) ∈ ℂm for all Y ∈ K (m fixed, Σm = 0).
- Calibration: m = e₀ − e₁ (solutions exist; our control rate was only 3/82, which is why our negatives
  are weak). Also dim 3 for every m.
- Runs: ≥ 20,000 starts for each of m = (1, ω, ω², 0, 0) with ω³ = 1; (1, i, −1, −i, 0);
  fifth roots of unity; (1, 2, −3, 0, 0); (1, 2, 3, −6, 0); (1, 2, 3, −1, −5); (1, 2, −4, 1, 0).
- Starting point: `verifyfl/r4_z4.py`, `verifyfl/di_gr.py`.

### C4. Exact algebra: Lemma Z (independent of the branches above, clean and self-contained)
- Claim: a 5×5 complex matrix g with all row and column sums zero and all twenty-five 4×4 minor
  permanents zero has a zero row or a zero column. Proved for rank ≤ 2 (`NOTES-lemmaz.md`).
- Computation: I = ideal of the 25 minor permanents in the 16 coordinates of g[0..3, 0..3] (the rest is
  determined by the centring). Saturate I successively by the ten ideals (entries of row i), (entries of
  column j); Lemma Z ⟺ the result is the unit ideal. Over 𝔽_p first (msolve / Singular / Macaulay2),
  then ℚ or several primes. Cheaper by strata: see `NOTES-lemmaz.md` section 5.

### C5. Scale-ups of searches that timed out here
- `stage3/s3_planes_z2.py SEED DELTA NVAN TIMELIMIT MAXNFEV` (weakened plane problem for a 2-dim
  single-row part, 148 real unknowns; never converged here). Spec: `NOTES-stage3.md` section 24 (C).
- `stage2/r6_census.py SEED NTRIALS MAXIT [DIMS]` and `stage2/r6_fk.py KIND SEED NTRIALS [MAXIT]`
  (5-dim 4×5 level spaces with all 4×4 column-deletion permanents of Y itself vanishing; then FO2 bound).
  Spec: `NOTES-stage2.md` R6-1..R6-8. Wanted: any solution with single-row and single-column parts of
  dim ≤ 2 and FO2 bound ≥ 9, or any solution not supported on a zero-block pattern.

## 3. Lean files to compile and check

All import only Mathlib and PEqualNP.Defs, contain no sorry / axiom / native_decide, and passed
`lake env lean` here on toolchain v4.36.0 with the repo at the commit of 19:50 today. Each ends in a
placeholder theorem (not the gap statement), so the repo's statement check will not match; the point is
an independent compile, the axiom list, and the format linter (`tools/check-lean.mjs`).

| File | Lines | Content |
|---|---|---|
| `lean/fl/FL.lean` | 4,928 | Lemma SL, Theorem FL (row and column), Lemma DS — no hypotheses |
| `lean/zbf/Zbf.lean` | 2,015 | R0, ZBF, Theorem B, Lemma C (all n), CA2, Theorem A, 3×3 bound |
| `lean/zbf/Zbf8.lean` | 4,866 | the above + N3′, C4, C7 (one explicit hypothesis), pigeonhole facts, part of Theorem G |
| `lean/zbf/FrameZbf.lean` | — | Frame210 + ZBF in one file |
| `lean/Frame210.lean` | — | bridge from the gap hypothesis to subpermanent sums; d = 0 case; `gap_of_S_wlog` |

Please report: compile time and result for each; `#print axioms` of the final theorem of each; linter
verdict; and the size in bytes (FL.lean is 214 KB, Zbf8.lean 232 KB — together already near the
512 KiB cap).

## 4. Bundle contents

- `BRIEF.md` — problem brief with eight dated updates (read first).
- `NOTES-*.md` — one file per helper; each has a RESULT block at the top.
- `<role>/` — that helper's scripts and data (`.py`, `.npy`).
- `lean/` — Lean sources (latest files; intermediate snapshots omitted).
- `handoff/HANDOFF.md`, `handoff/oracle.py`.
- `L-gct-086/` — notes from the earlier attempt on the general-n statement.
