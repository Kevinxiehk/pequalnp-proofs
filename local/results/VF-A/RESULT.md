# VF-A — one-vector extensions of the four isotropic planes N (COMPUTE-verifyfl.md A)

**Verdict: UNIT IDEAL for all four (beta, xi), at 4 independent primes. Calibration non-unit at all 4 primes.**
So (modulo the char-0 caveat below) no 3-dim space with defect in C m contains any of the four N, for m = (1, w, w^2, 0, 0).

## What was run (local, 2026-11-23 ~18:45 UTC)
- `gen.py P CASE OUT SEED` (pure Python, own modular polynomial arithmetic) builds the system mod P and writes msolve input.
  - i, sqrt3, w = (-1 + i sqrt3)/2, beta = +-sqrt3/4, xi = +-sqrt(-3/(32 beta)) computed in F_P (Tonelli-Shanks).
  - Z = h0 m^T + chi1 (0, xi, -xi, 0, 0)^T, h0 = one/4 + beta chi2;  Zs = chi1 mbar^T (exactly the spec / r4_pr3.Nplane).
  - E in A_m parametrised by rows 0..2 free (15 vars) and lambda (row 3 = lambda m - rows 0..2): 16 unknowns e0..e15.
  - R_i = sum_j W_ij (C_j(Y) - 24), Y = k Z + t Zs + x E, W = basis of {w : w.m = 0} = {e3, e4, (w,-1,0,0,0), (w^2,0,-1,0,0)}.
  - Equations: every coefficient (in k, t, x) containing x, of R_1..R_4 (64 nonzero polynomials, degree <= 4 in E),
    plus one generic linear equation per generator of N (2) and one generic affine equation (E = 0 excluded).
  - CASES A1..A4 = (beta sign, xi sign) in {++, +-, -+, --}; CAL = N replaced by span(Zs) (spec's calibration).
- `msolve -g 2` (reduced DRL Groebner basis), msolve 0.6.5 (Ubuntu package).

## Checks
- Sanity: in every case the x-free part of R_i(k Z + t Zs) is identically 0 mod P, i.e. N has defect in C m exactly
  (confirms my N equals yours).
- Calibration CAL (must be non-unit): basis of 83 elements, NOT [1], at all 4 primes.  (CAL_2147483629.gb attached.)

## Results (basis returned by msolve)
| prime P | CAL | A1 (++) | A2 (+-) | A3 (-+) | A4 (--) |
|---|---|---|---|---|---|
| 2147483629 | 83 elts | [1] | [1] | [1] | [1] |
| 2147483497 | 83 elts | [1] | [1] | [1] | [1] |
| 2147483077 | 83 elts | [1] | [1] | [1] | [1] |
| 2147483053 | 83 elts | [1] | [1] | [1] | [1] |
Each run < 0.2 s. Primes: P = 1 mod 12 with -3/(8 sqrt3) a square (so all constants exist in F_P); different random
normalisation seeds per prime.

## Caveats
- **Dimension count in the spec:** A_m has dimension 16, not 17 (20 entries, 4 constraints "column sums in C m";
  your di_ext.ambient_m gives 16 too), so 16 - 2 - 1 = 13 effective unknowns. Harmless.
- **Char 0:** unit mod 4 random large primes is overwhelming evidence, not a proof, that the ideal is the unit
  ideal over Q(i, sqrt3, xi) (a char-0 solution would survive reduction at all but finitely many primes).
  If you need it exact, I can redo it in Singular over Q(theta), theta a primitive element of Q(i, xi) — say so in QUESTIONS/REQUESTS.
