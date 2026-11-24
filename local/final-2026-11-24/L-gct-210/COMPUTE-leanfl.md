
## ROUND 9 (UTC 23:5x): exact classification of isotropic pairs for TC5 (P3)  [leanfl/sing9/]
- Question: v, w isotropic in V = {tau = 0} (<x,x> = 0), distinct lines, tau(v w^2) = tau(v^2 w) = 0 (NO bracket condition).
- Method: V = span(h1,h2,h3), h1 = (1,1,-1,-1), h2 = (1,-1,1,-1), h3 = (1,-1,-1,1); isotropic conic a^2+b^2+c^2 = 0 parametrised
  by (a,b,c) = (1-t^2, I(1+t^2), 2t), t in P^1 (t = oo: (-1,I,0)). Singular 4.3 over Q(I) (minpoly I^2+1), saturation by t-u,
  minAssGTZ; chart t = oo separately. Files pairs.sing / pairs2.sing / pairs3.sing (+ .log), chk_pairs.py (sympy re-check). < 1 s, < 50 MB.
- Result (exact): the relation is 7 unordered pairs on 14 DISTINCT lines (the degree-13 polynomial of the affine t-values is
  squarefree, plus t = oo):
  (A) 3 pairs of chi_1-type lines {0,oo}, {1,-1}, {I,-I}: the six chi_1-type lines (permutations of (1,i,-1,-i)) paired as
      w = c v^3 (v o w constant); {I,-I} = (chi_1, chi_3).  These 3 pairs form ONE S_4-orbit.
  (B) 4 zero-row pairs: for each k the two isotropic lines of V cap {x_k = 0} (t-values = roots of t^2 + (+-I+-1) t + ...).
  Every isotropic line lies in AT MOST ONE related pair, so three pairwise related distinct lines do not exist.
- Calibration: (chi_1, chi_3) appears (t = -I, I); zero-row lines appear with exactly one zero coordinate (chk_pairs.py); f1 = f2 = 0
  re-checked symbolically at all 7 pairs.
- Comparison with verifyfl DI5.3 (P3): the paper lists antipodal pairs "th' = -th, th^4 = -4" (2 pairs) + 4 zero-row pairs; the exact
  list has ONE MORE chi_1-type pair (presumably th in {0, oo} of the paper's chart). It is in the same S_4-orbit as (chi_1, chi_3),
  so no new branch is needed: (P3)'s two conclusions (two-equal-lines case "up to S_4"; every th in exactly one pair) still hold.
- Hand proof found for Lean (no Groebner certificate of the classification needed): with y_k := v_k w_k and g := <v,w> (!= 0),
  the s^2-coefficient of Newton's identity for u = v + s w gives 6 y_k^2 - 2 g y_k independent of k, so y takes <= 2 values with
  sum g/3; with sum_k y_k = g and sum y_k v_k = sum y_k w_k = 0 this leaves exactly: (i) v o w = (g/4) 1 (then e3(v) = 0, v chi-type,
  w = c v^3), or (ii) one k with v_k = w_k = 0.
- Calibration 2 (sing9/calib.sing): adding the bracket condition br(v,v,w,w) = 0 leaves exactly the 4 zero-row components and kills the
  chi_1 pairs (br(chi_1,chi_1,chi_3,chi_3) = -24 + 32 = 8) -- in agreement with the already Lean-proved HypIIa (v o v ~ w, w o w ~ v).

## ROUND 10 (UTC 00:58): exact check for TC5 (P4) branch (c3), part 2  [leanfl/sing10/]
- Question (the S4 fact "DC strongly level planes of types I, II have <= 2 lines" used by verifyfl DI5.3 (c3)): is there a 2-dim
  space N'' of 4x5 matrices, strongly level, rs = 0, columns 0 = 1 (= u = -(y_2+y_3+y_4)/2), whose neutral columns y_j = c_j v_j lie on
  three PAIRWISE DISTINCT isotropic lines of V, all three columns active?
- Method: lines v_j = (1-t_j^2, I(1+t_j^2), 2t_j) in the h-basis (and the point t = oo for at most one line); planes of coefficient
  vectors: chart A c_4 = al c_2 + be c_3 ((al,be) != 0, split al != 0 / al = 0 & be != 0), chart B c_3 = al c_2 (al != 0), c_4 free;
  strong levelness = for each deleted column (0, 2, 3, 4; 1 = 0) X2 = X3 = perm = 0 identically in the plane parameters (s,t).
  Singular over Q(I), saturation by pairwise distinctness of the finite t_j and the chart's non-vanishing; 12 runs, each < 1 min,
  < 100 MB (sing10/c3plane.py generator, runall.sh, runall.log).
- Result: every chart gives dim = -1 (unit ideal): NO such plane exists.
- Calibration: the same equations vanish identically on the known type-I plane chi_1 (x) {c_2 + c_3 + c_4 = 0} (one line, u = 0;
  verifyfl's example L'_4), i.e. the generator recognises a genuine strongly level plane; it is excluded only by distinctness.
- Consequence: (c3) with E(z) = 0 reduces to this fact once d(N) = zeta is shown (verifyfl: (Z2) gives d'(Z) orthogonal to v_3, v_4,
  v_5, which span V). For Lean the fact still needs a hand proof (or a certificate); recorded as the open (c3) step.

## ROUND 11 (UTC 01:20): exact certification of the DI5.3 (c2) closed forms  [leanfl/chk_c2.py, sympy over Q, exact]
- Setting: neutral columns y_3 = l3 v, y_4 = l4 v, y_5 = b v' (v, v' isotropic in V), a = l3 + l4, u = -(a v + b v')/2,
  t3 = tau(v^3), t21 = tau(v^2 v'), t12 = tau(v v'^2), t03 = tau(v'^3), g = <v,v'>.
- Verified identically (with tau v = tau v' = 0 substituted): tau(u^2 v) = (a^2 t3 + 2ab t21 + b^2 t12)/4,
  tau(u^2 v') = (a^2 t21 + 2ab t12 + b^2 t03)/4, tau(u v^2) = -(a t3 + b t21)/2, tau(u v v') = -(a t21 + b t12)/2,
  -2 Tbar_1 = l3 l4 (a t3 - b t21) + a b (a t21 + b t12), Tbar_5 = a tau(u^2 v) + 2 l3 l4 tau(u v^2),
  Tbar_3 = l4 tau(u^2 v) + b tau(u^2 v') + 2 l4 b tau(u v v'), Tbar_4 = same with l3 (Tbar = X3c/2 of the deletion);
  and, modulo <v,v> = <v',v'> = 0 (Groebner reduction), the bracket [u,z3,z4,z5] = l3 l4 b (3 tau(v^3 v') a + (3 tau(v^2 v'^2) - g^2) b).
  All 9 identities TRUE: the paper's closed forms are exact.

## Round 12: (F1) by ideal membership (leanfl/sing12/, Singular over Q, < 1 s each, < 0.5 GB)
- I = (tau v, tau w, <v,v>, <w,w>, tau(v^2 w), 3 tau(v^2 w^2) - <v,w>^2) in Q[v0..v3, w0..w3].
- f1.sing: I + (1 - y g v0v1v2v3) = (1)  (g = <v,w>), i.e. g v0v1v2v3 in rad(I).
- f1c.sing: smallest powers: g^3 (v0v1v2v3)^2 in I; g^3 w_k^2 in I + (v_k) for each k (k = 0..3).
- f1e.sing: lift certificates (8 variables) -> sing12/f1_P.txt, f1_w0..3.txt; leanfl/gen_f1.py re-checks each identity with sympy
  (exact) and writes lean/fl/p5i.part (certificates scaled by 8, integral). So (F1) [distinct isotropic lines with tau(v^2 w) = 0 and
  [v,v,w,w] = 0 form a pair with a common zero coordinate] is now an exact Lean lemma (F1_zero_row), not a resultant computation.
07:40 round 15: leanfl/cert/sweep1.sh (Singular lift mod P1 on 5 sample UNIT charts: pt2 01_01_01, rows B3_000_f0, vf A2 chart13, stage3 fc_FULL_00001, symdc piv029), 1 core, ulimit -v 0.5 GB, 30 min/chart, log leanfl/cert/sweep1.log. Also cc34 chart 0123 lift over Q and P1 (0.01 s each).
07:42-07:55 round 15: leanfl/cert/sweep2.sh (lift mod P1: rows B3_000_f0 = NOT a unit chart, OOM; vf A2 chart13 26 terms; stage3 fc_FULL_00001 3627 terms 0.5 s), stdpt2.sh (pt2 chart: Singular std > 300 s at 0.5 GB, msolve 21 s), dc3job0/1.sh (DC3 m12m3 at P1 regenerated with verifyfl/exact/gen_n1s.py into leanfl/cert/dc3/, Singular lift on 30 sampled UNIT charts, 60 s / 0.5 GB each). All 1 core each, done.
08:04 round 15: all leanfl jobs stopped (none running). STOPPED.
