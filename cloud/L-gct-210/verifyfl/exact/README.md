# verifyfl/exact — exact (Groebner) generators for (SL_m); state at hand-over (2026-11-23 20:35)

Run with `python3 -I`; every script adds its own directory to sys.path.  Engine: msolve (`MSOLVE=/path/to/msolve`, default
/home/claude/tools/gb/msolve), input format = that of coord/local/results/VF-A/gen.py (variables / characteristic / polynomials).
Mathematics and notation: ../../COMPUTE-verifyfl.md (section 0 and "NEXT"), ../../NOTES-verifyfl.md (DI5-R5, DI5-R6).

| file | what | state |
|---|---|---|
| exactlib.py | modular polynomial arithmetic; `equations(B, W, p)` = all coefficients of R_i(sum_r x_r B_r); parametrisations; msolve writer/runner; rref mod p | TESTED: coefficients reproduce R numerically (m12m3, iso, SL) |
| gen_n1.py | [DC-k] unstructured: all reduced-echelon cells of Gr(k,12) (mode `dc`) or of Gr(k,9) for 3-column spaces (mode `3col`, Lemma 3C cross-check) | TESTED by substitution (test_gens.py: 9/9, both directions) |
| gen_n1s.py | [DC-k] structured for defect lines on columns 0,1,2 (also SL, two): rank rho of the neutral-column map, N_P in Gr(k-rho,6), isotropic-line charts ab / z1 / z2; optional `split` A/B of the case N_P = C Z_0 | TESTED by substitution (test_gens2.py: 7/7); split A/B only smoke-tested (SL: unit) |
| test_gens.py, test_gens2.py | substitution tests (no engine): known spaces satisfy every equation of their cell, random points do not | pass at p = 2147483629 |
| gen_n2.py ([T31]), gen_n3.py ([T22]) | NOT WRITTEN. Spec: COMPUTE-verifyfl.md NEXT N2, N3; control for both: the exact space K_2 below | - |

Commands (cells are numbered as printed by the manifest; `run` calls msolve and deletes files whose verdict is UNIT):
    python3 -I gen_n1s.py 2147483629 m12m3 3 OUT run timeout=600        # [DC3] structured, 254 cases; m presets: exactlib.PRESETS
    python3 -I gen_n1s.py 2147483629 m12m3 3 OUT rho=2 run timeout=600   # only the rank-2 cases
    python3 -I gen_n1.py  2147483629 m12m3 3 dc   OUT 0 220 run           # [DC3] unstructured, 220 cells (about 1 min per big cell)
    python3 -I gen_n1.py  2147483629 m12m3 4 3col OUT run                 # Lemma 3C cross-check: must be UNIT in all 126 cells
    python3 -I gen_n1.py  2147483629 SL    3 dc   OUT 0 220 run           # Lemma SL cross-check: must be UNIT
Primes used so far: 2147483629 only (others = 1 mod 12: 2147483497, 2147483077, 2147483053).

Verdicts recorded in run/*.manifest  [all MODULAR, one prime, msolve 0.10.1]:
 * 3col, k = 4, m = (1,2,-3,0,0) and (1,w,w^2,0,0): UNIT in all 126 cells            (= Lemma 3C, hand-proved; pipeline calibration)
 * 3col, k = 3, m = (1,2,-3,0,0): cell 0 NON-unit (129 basis elements), as it must be (run interrupted after cell 1)
 * [DC3] structured, SL: UNIT in all 254 cases                                       (= blueprint Lemma A, Lean-checked; calibration)
 * [DC3] structured, m = (1,2,-3,0,0): UNIT in 252 of 254 cases; the 2 others TIMED OUT and are kept as
     run/n1s_m12m3_p2147483629_k3_rho2_piv0_l0_ab_ab.ms (19 unknowns; > 115 s in the older th-chart)   <- DECISIVE, run it first
     run/n1s_m12m3_p2147483629_k3_rho2_piv1_l0_ab_ab.ms (18 unknowns; the same cell was UNIT in 11.6 s in the th-chart)
 * [DC3] unstructured, m = (1,2,-3,0,0): cell 0 (27 unknowns) UNIT in 54 s; cell 1 timed out at 60 s; rest not run.
 * an earlier run with the legacy charts (th/c3) gave for m = (1,1,-2,0,0) and for SL: UNIT in 133 of 134 cases, the generic
   rank-2 cell timing out at 12 s (manifests of that run were deleted when the charts were changed; redo with the commands above).
Decision rule: all cases UNIT for m  =>  [DC3] for m (no 3-dim doubly centred space with defect in C m; kills types (1,3), (0,4)).

Exact control space for [T22]/[T31] (two-column line m = e_0 - e_1; verified numerically to 1e-13, not yet mod p):
    K_2 = span( zeta (e_0 - e_1)^T,  zb e_2^T,  zb e_3^T,  h e_3^T ),  zeta = (1,w,w^2,0), zb = (1,w^2,w,0), h = (1,1,1,-3)
is a 4-dim column-centred space with defect exactly C (e_0 - e_1): type (q,d) = (2,2), row sums = zb^perp.  Any correct [T22]
generator must find it (non-unit cell); gen_n1s k = 2 contains its doubly centred part (type II plane, tested).
