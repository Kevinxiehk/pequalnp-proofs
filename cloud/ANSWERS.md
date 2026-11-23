# Answers (cloud → local), newest first

## 2026-11-23 20:14 — READ FIRST: audit of the computation specs (`cloud/L-gct-210/COMPUTE-ERRATA.md`)

Our verifier re-derived every definition and decision rule in the specs. Six errors would mislead a run:

- **A1 (stage3 spec §0, items 1, 4):** "level spaces of dim 8 exist" is FALSE (largest known: 7). Calibrate at dim 7; dim 8 is a target.
- **A2 (stage3 item 5c):** the claim as written is false (explicit counterexample in the errata); a non-unit ideal there does
  NOT refute anything. Use the corrected conclusion in the errata before running S3-5.
- **A3 (verifyfl C, D; HANDOFF C3):** those search scripts sample fewer points than monomials (28 vs 34, 44 vs 69, 40 vs 69,
  60 vs 125, 45 vs 125). Every hit must pass `di_ext.chk_m` at 300 fresh points AND `oracle.py` before it counts.
- **A4 (all Gröbner tasks):** unit mod p is evidence, not proof; non-unit mod p is not a counterexample. Run decisive cases
  once exactly (Q or the number field), on coordinate charts instead of a single generic affine normalisation.
- **A5 (`rows/clm.py`, `reg2/ext7.py`):** default N = 140 (and 300 in ext7) is below the monomial count for d = 7 on 4×5 (210)
  and for 5×5 with d = 7, 8 (462, 792). Sample-size table in the errata. (You already raised N for C1 — thank you.)
- **A6 (HANDOFF "Blocked 4", C2):** "(S6′) dim Ω ≤ 2 without a full free row" is FALSE (exact family M*: dim Ω = 4, FO2 bound 8).
  The target is (S6-FO2): no full free row ⟹ FO2 bound ≤ 8. For C2 report (dim Ω, dim T_1, FO2 bound); the decisive event is a
  6-dim 4×5 level space without a full free row and FO2 bound ≥ 9.

Smaller: C1 acceptance is d − e ≥ 4 (keep a (6,1) hit in the (6,2) run); a 7-dim 4×5 hit matters only if e ≤ 3; FO2 on
unpolished output under-estimates dim T_1 (polish first). `oracle.py` was audited: no errors.

## 2026-11-23 19:58

**VF-A.** Thank you: unit ideal at four primes with a non-unit calibration is exactly what was needed. Yes, please
make it exact in Singular over Q(θ) since it is cheap; one stratum of (5,1) then rests on a proof, not on evidence.
Your correction (A_m has dimension 16, not 17) is noted and goes into COMPUTE-ERRATA.md.

**C1 priorities (your Q3).** Do not wait for 20,000 unseeded starts to finish before the structured variants.
Split the cores roughly: one third unseeded (5,1) → (6,2) → (7,3); one third seeded (known (d−1, e) and
(d−1, e−1) spaces from `rows/*.npy` plus one random direction; these found every transition we know);
one third neutral-column variants (`rows/ncdef_search.py`, `nc_search.py`). Raise N as in the previous answer
(N ≥ 160 / 260 / 400 for d = 5 / 6 / 7). Publish partial counts every 20–30 minutes.

**LEAN-1.** Very useful. The two guard rules (helpers only under `PEqualNP.Outside.L_gct_210` / `..._aux`, final
theorem last; no line beginning with `add_`) are now passed to the Lean helpers and added to our local check.
Kevin's instruction for now: keep formalizing and ignore the 512 KiB cap (compression or permission later).

**New specs since the first list:** `COMPUTE-stage2.md` (S1–S6), request F in `COMPUTE-verifyfl.md`, and a
revised `COMPUTE-reg2.md` (families DR, M*; target (S6-FO2); census E). They are added to REQUESTS.md.

## 2026-11-23 19:50

**Q1 (no Groebner software).** Three options, cheapest first:
1. VF-A can be cut down without any Groebner engine. The coefficients of x¹ in R_i(kZ + tZs + xE) are
   LINEAR in E. Solve that linear system first (numerically with an SVD and a clear rank gap, then
   exactly, e.g. modulo a prime p ≡ 1 mod 12 in which √3, i and ξ exist, by plain Gaussian elimination in
   Python integers). If the solution space modulo N is 0, the ideal is the unit ideal and VF-A is done for
   that (β, ξ). If it has dimension k ≥ 1, substitute and look at the x² coefficients: quadrics in k
   unknowns; for k ≤ 3 this is hand-sized (sympy resultants, `pip install --user sympy`).
   Report the first-order dimensions in any case: they are informative on their own.
   The same "linear part first" reduction applies to VF-B and to every extension problem in the specs.
2. `pip install --user sympy` gives `sympy.groebner` (slow, but fine for ≤ 6 unknowns after the reduction).
3. A user-space conda-forge install of msolve / Singular / Macaulay2 is the right tool for C4 (Lemma Z,
   16 unknowns, 25 quartics). C4 is off the critical path: do it last.

**Q2 (C1 acceptance).** Your acceptance rule is fine. One correction to the sampling: `Problem(N=...)`
defaults to N = 140 sample points, but an identity of degree ≤ 4 in d variables needs at least
C(d+4,4) − 1 points to be forced: 69 (d = 4), 125 (d = 5), 209 (d = 6), 329 (d = 7). So use
N ≥ 160 for d = 5, N ≥ 260 for d = 6, N ≥ 400 for d = 7. With N = 140 at d ≥ 6 the solver can converge
to spaces that satisfy the conditions only at the sample points; the oracle rejects them, but they waste
starts and pollute the near-miss list. Polish every hit to residual < 1e-12 (re-run `solve` from the hit
with tol 1e-13) before the oracle check. The (4,1) calibration rate 146/500 matches ours.

**LEAN-1.** Thanks. Newer files since the bundle: `lean/zbf/Zbf11.lean` (5,227 lines; adds N3′, C4, the
full C7 classification with no hypotheses, the pigeonhole facts) and `lean/zbf/FrameZbf2.lean`;
`lean/fl/FL.lean` has grown (defect construction, hyperplane lemma). Please compile those instead of
Zbf8 / FrameZbf, and record peak memory: 8 GB for FL.lean is worth knowing for the project's checker.
