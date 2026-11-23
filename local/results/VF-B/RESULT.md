# VF-B — the N-problem for |P| = 4, 5 (COMPUTE-verifyfl.md B)   [PARTIAL: calibration done, main cases running]

## Method
`gen.py P m OUT SEED` writes a Singular script over F_P (P = 2147482921 = 1 mod 60, so i, w, fifth roots exist):
- Z, Zs supported on the columns P, parametrised by (1): rows 0..2 x columns P[:-1] free, the rest from row sums 0 and column sums
  m_j (Z) / 0 (Zs): 3(p-1) free unknowns each (12 / 18 / 24 for p = 3 / 4 / 5).
- (2): every coefficient in (k, t) of R_i(k Z + t Zs), R_i = sum_j W_ij (C_j - 24), W = basis of {w : w.m = 0}.
- (3): <z0_j, z0_j> = (3/4) m_j^2, <zs_j, zs_j> = 0, <z0_j, zs_j> = 0 for j in P.
- gauge: one generic linear equation on Z (= 0) and one generic affine equation on Zs (= 1).
- (4): successive saturation by the ideals (entries of zs_j), j in P (Singular 4.3.2 `sat`), then std.

## Calibration (|P| = 3, 12 unknowns) — PASSED
- m = (1, 2, -3, 0, 0): after saturation **unit ideal** (required by Theorem PR3).  [before saturation: dim 0, not unit]
- m = (1, w, w^2, 0, 0): after saturation **dim 0, vdim 24**. Independent check (`calpts.py`): the four planes N of VF-A, under all
  24 row permutations and brought to the same gauge, give exactly **24 distinct points, and all 24 lie on the variety**.
  So the solution set is exactly the row-permuted A planes, as required.

## Main cases (running since 18:54 UTC, Singular, 3 at a time, 3 h timeout each)
(1,2,3,-6,0); (1,2,-4,1,0) [expected non-empty]; (1,1,1,-3,0); (1,1,-1,-1,0); (1,i,-1,-i,0); (1,2,3,-1,-5); (1,1,1,1,-4);
(2,2,2,-3,-3); (1,z,z^2,z^3,z^4).  Results will be added here.
