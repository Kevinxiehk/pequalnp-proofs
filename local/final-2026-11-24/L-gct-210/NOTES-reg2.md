# NOTES-reg2 (role reg2; start 18:47, budget 100 min -> ends ~20:27). Regime: some row/column with a_r >= 2.
## RESULT ROUND 20 (reg2, 07:57-08:03 UTC, ABORTED; section 28)
 R20-1 [rigorous + exact, 28.1] the 3100|10000 R1 census family (dr35_u3_*) is ONE rigid space c3100 over Q(w): level, dim T_1 = 10,
      rank q = 4 => FO2 = 8 exactly (at the bound, not above).  N element on that pair and the other census families: not done.
## RESULT ROUND 19 (reg2, 07:09-08:00 UTC; section 27)
 R19-1 [rigorous, 27.1] RANK-ONE LEMMA, partial (rows; columns by transposition).  With U' = row-line span of the two other rows:
      z = x + y lies in V cap U'^perp; dim U' = 4 => z = 0; dim U' = 3 => z = gamma mbar and gamma = 0 under (3a) or (3b); U' = H_c with W_c
      onto C^{P,Q} => no genuine two-row element; U' = H_c and some v_P != v_Q => no R1.  Application: 2100|20000 R1, class 00 (ext_9..11
      family) is rank one off dim U' <= 2.  Mixed-P_k formulas brute-force checked.
 R19-2 [27.3] all known genuine e = 5 members have FO2 <= 8: ext_9..11 and dr35_u2 (9,3,7), dr35_u3_116/_29 (10,4,8) -- AT THE BOUND.
 R19-3 [exact, 27.4] (3,1|2) along (1,1,1) CLOSED: exact triviality at the w-points over QQ<sqrt(-3)>.
 R19-4 [exact, 27.5] R3 cone argument needed ABSOLUTE irreducibility (gap); checked: case (II) at both B and case (alpha): every quadric has
      Hessian rank 3 => valid.  R3 (alpha) closed at its point.
 R19-5 [27.6] R3 (I) at its point: V_B contains five 3-dim linear spaces (exact over Q) -- all degenerate (P_0 of rank 2 modulo Lin(M),
      e = 4, FO2 7); mod two primes nothing else is linear.  Small remaining gap (another Qbar-space with the same reduction).
 R19-6 [27/COMPUTE 13] exact rank-one split (RANK1SPLIT) and Lemma split (DROPU) in twostage; both time out (120-400 s) on member types.
 R19-7 [rigorous, 27.7] LEMMA ISO (t isotropic != 0 => t o t not in span(1,t)) + LEMMA INT (dim U' = n-2 and U_k cap U_l != 0 => z = 0):
      G is rank one EVERYWHERE for other-row lines (3,1) [dr35_u3 family] and column (2,1,0), (3,0,0); for (2,2) [dr35_u2 family] and column
      (1,1,1) except one explicit isotropic locus.  42 of 630 classes.  DROPU part B on 2200|10000 class 11 hit the 0.5 GB cap (halt 14).
## RESULT ROUND 18 (reg2, 06:16-07:10 UTC; section 26)
 R18-1 [numerical measure, 26.1] QUADRATIC stage at generic points of every stage-1 component, gauge = row lines on the pair + ALL cross-line
      combinations on the pair: NONE of the 630 classes keeps a genuine solution at a generic point (487 die at the linear stage -- C1 125,
      R1 102, N 260 of which 82 have s = 0 forced -- and 143 at the quadratic stage).  R17-2's "264 with a free direction" were mostly gauge.
 R18-2 [26.6] BUT generic kills do not close types: genuine e = 5 spaces exist on rank-drop loci (census ext_9..11 = 2100|20000 R1 on the
      line-free rows, dr35_* = 2200|10000, 3100|10000; level 1e-12; FO2 7).  A global solver with the rank-one ansatz y = -x finds them
      ((9,3,7), validation log); every known genuine e <= 5 element is rank one.  Two global sweeps (with / without ansatz) running.
 R18-3 [rigorous, 26.2] Lemma N0: if Lin(M) has an element on lines P, Q with nonzero row sum (e.g. a free column), N on P, Q reduces to R1.
      Lemma N1: column-line conditions on N (two column lines with independent (v_P, v_Q) force (x_c, y_c) = (s, -s)).  ntype1's N is rank one.
      No support lemma of the form "N forces lines on its rows" found.
 R18-4 [26.3] twostage.py genuineness FIXED before REG2-E5-BATCH starts (R1/C1: x not in U_P, y not in U_Q via maximal minors; the old
      version passed G in Lin(M) and gave NONEMPTY for every class with lines on both lines).  Old EMPTY verdicts remain valid.
 R18-5 [exact, 26.4] CORRECTION: the R3 cone result of 24.5 belongs to case (ALPHA) (closed at its rational point); case (I) is OPEN.
 R18-6 [exact, 26.5] (3,1|2) along (1,1,1): all 15 components handled -- t = 0, fixed points (-1,0), (-2,0) t = 0 only, (1,-3) UNIT; the four
      w-points carry a TRIVIAL deformation [numerical].
## RESULT ROUND 17 (reg2, 05:43-06:16 UTC; section 25)
 R17-1 [exact, 25.1] e = 5 STAGE 1 over all 296 types / 1370 classes: 452 classes have NO 5-dim level line configuration (stage-1 kill),
      214 incidence kills, 66 orthogonality type kills; 630 classes have line components, 74 stage-1 timeouts.  (Pre-checks alone had left 1156.)
 R17-2 [numerical measure, 25.3] linearised stage 2 at random points of the line components (gauge removed): 366 classes have NO free genuine
      direction generically (members only on rank-drop subloci, e.g. ext_10), 264 classes have one (mostly N-type pairs; R1 on two line-free
      rows survives in 1 class only).  The exact rank-drop computation exceeds 0.5 GB as set up (25.6).
 R17-3 [exact, 25.5] (3|3) row deformations with free S CLOSED (5 leftover directions, each UNIT or t = 0); (3,1|2) along (1,1,1): visible
      leftovers closed (two points t = 0 only, (0,w),(0,w^2) trivial deformations), full leftover list being recomputed.
 R17-4 cutting lemmas: none proved; the data say an N-element lemma would cut most (about 2/3 of the 264).  R3 (alpha): pool still running.
## RESULT ROUND 16 (reg2, 03:55-05:42 UTC incl. a usage-limit cut ~04:25-05:15; section 24)
 R16-1 [exact, 24.4] the two remaining new families are CLOSED: 2121Vni row 0->1 and 2211BD row 0->1 (pool omega_e0 + chart-2 lines +
      point certificates).  With 21.5/22.3/22.6/23.1 the spanning-set and 3-dim-part deformations are closed except the items listed in 22.6.
 R16-2 [24.0] CORRECTION: ntype1 has rank q_Y = 4 (verify2), not 5; q_rank_exact.py rewritten with DomainMatrix over QQ<sqrt(-3)> (rank 4 for
      three Y); FO2 <= 8 -- still closed.
 R16-3 [24.1] e = 5 type solver: pre-checks alone kill 66/296 types (orthogonality of line parts) and 214/1370 incidence classes (incidence);
      1156 classes need Groebner work; direct and two-stage runs time out (stage 2 = genuine element over a non-linear line component).
 R16-4 [24.2] N type: in ntype1's support chart the system has only ntype1; the 2 extra tangent directions leave that support (chart with
      column-4 entries queued, REG2-NTYPE4).
 R16-5 [24.5] R3 case (I) at a rational point: no M (cone = 5 irreducible components of dim 3, degree 2); case (alpha) running.  [CORRECTED round 18 (26.4): the cone output belongs to case (ALPHA), not (I); case (I) did not finish (halt at the cap).]
 R16-6 cutting lemmas ("R1 => rank one isotropic", phi = 0, (BL) existence): NOT proved this round.
## RESULT ROUND 15 (reg2, 03:38-04:00 UTC, Lean window 3: light runs; section 23)
 R15-1 [23.3] COMPLETENESS, stated explicitly: the list to verify is the set of COMBINATORIAL TYPES of Theorem 19.3 (conditional on (BL)),
      each solved exactly; deformation scans only find components.  They are incomplete in principle: (G3) other skew shapes (open, never
      observed), (G4) spaces with NON-level base -- REAL (the N type), (G5) simultaneous multi-part deformations beyond the scanned pairs;
      (G6) 4-dim parts are outside (S6-FO2) by FL.  e = 6 is complete; e <= 5 is NOT exhausted -- the next tool is a type-by-type solver.
 R15-2 [exact, 23.2/23.4] the N-type space ntype1 (rigid part fixed over Q(w); unique): level, dim T_1 = 10, rank q_Y = 5 => FO2 <= 7.  [CORRECTED round 16: rank q_Y = 4, FO2 <= 8 -- still closed]
      The rows-team N spaces fit it at 3.4e-6; the type has a 2-dim tangent space beyond gauge (23.5) -> probably a 2-parameter family.
 R15-3 [exact, 23.1] (3|3): the column 3-dim deformations (direction (3,2,1)) UNIT; the row ones (free S) numerically inside 213def,
      exact certificate queued.  [23.0] the (2,1|3) line runs are level (0 level equations, printed).
 R15-4 [23.6] "R1 => rank one isotropic": conjecture (6/6 instances), not proved.
 R15-5 [23.8] the list is finite but large: e = 5 alone has 29 line patterns and 296 types; needs an automatic type solver or cutting lemmas.
 Pool chain (not started, window): REG2-DEFOSPAN(-MINORS), REG2-R3-CONE, REG2-DEFO3-312, REG2-33ROW.
## RESULT ROUND 14 (reg2, 02:53-03:40 UTC, Lean window 3: light runs; section 22)
 R14-1 [numerical, 22.1] all 7 one-block rows-team spaces identified by Grassmannian fitting: nc_s21 in 2121V0 col 4->3 (closed), the 6 "PFC"
      spaces in 213def (closed -> covered UNCONDITIONALLY), nc_s17 in the new 2121Vni row 0->1 (open, queued), nc_s20 and seed_t3 in a NEW
      family (below); seed_t1, t6, clm_s3 are N-type (22.4).
 R14-2 [!! second gap, 22.2] skew deformations of 3-DIM line parts (rank-2 maps B = adj(G) S) were never scanned.  New scan defo_scan3.py:
      families for (3|2,1)a, (3|1,1,1), (3,1|2), (2,1|3) column part, BLOCK.  CLOSED exactly this round: all (3|2,1)a ones (generic direction
      for all p, free-S families at p = -1, 0 with 12 direction checks), all (3|1,1,1) points, all (2,1|3) column-part families
      (22.3, 22.6).  OPEN: (3,1|2) along (1,1,1) (queued), its conic components, BLOCK loci, 3-dim parts of (3|3), (1,1,1|3), (3,1|1,1).
 R14-3 [22.4] the N type exists (seed_t1-type: N + rank-one R1 on one row pair, not a deformation of a level base); every census R1 element
      is rank-one isotropic.  N-type families: to be built.
 R14-4 [22.5] (BL): route sketched (line element or N-piece existence, then induction on 6 - e); nothing proved.
 Open certificates still waiting for the pool (window): REG2-DEFOSPAN(-MINORS), REG2-R3-CONE, REG2-DEFO3-312.
## RESULT ROUND 13 (reg2, 02:07-02:55 UTC, Lean window 3: light runs only; section 21)
 R13-1 [rigorous + exact, 21.1] ALL 29 hit-free line patterns settled: (2,2,1,1|) by orthogonality + power sums (Newton), (2,2,1|1) class 110 and
      (2,1,1,1|1) class 1001 by orthogonality reductions to small exact systems over Q(i).  => (S6-FO2) holds for EVERY line-spanned 6-dim
      4x5 level space (leaf 11 item (v) closed).
 R13-2 [!! gap found, 21.4-21.5] the round-8 deformation scan skipped single-line parts written as SPANNING SETS (13 families).  Re-scan
      (defo_scan_span.py, three charts): new level-for-all families 2121Vni row 0->1, 2211BD row 0->1, 2121Vnii_xinf row 0->1 (213 row 0->1
      was known); all genuine special points certified exactly (19 point families, dim T_1 <= 9, or (10,4,8) with rank q >= 3 for 2211BD
      at (1,1)); 2121Vnii_xinf row 0->1 closed; s^2+s+1 / conic loci are trivial deformations; no new double deformations.
      OPEN: 2121Vni row 0->1 and 2211BD row 0->1 (2 parameters + t; numerically (9,3,7)) -> queued.
 R13-3 [21.2] rows-team spaces: 6 line-spanned, 6 contain a free column on four rows (stage3 LEMMA PFC: dim <= 8 modulo the (5,1)_{m0} leaf;
      FL itself does not apply), 7 one-block spaces (presumably in R13-2's families).  The earlier 1e-7 classification undercounted lines
      (files stored to ~1e-6).
 R13-4 [21.0] empty-output wrapper: cause = Singular's "redefining" warnings (elim.lib + primdec.lib) filling the first 6000 characters that
      the wrapper printed; no other driver affected.
 R13-5 [21.6] R3 cases (I), (alpha): scripts ready (B-spaces 4- and 6-dim), runs halted at the window cap -> queued REG2-R3-CONE.
## RESULT ROUND 12 (reg2, ~01:12-01:50 UTC; section 20)
 R12-1 [exact, 20.1, partial] R3 case (II) (n = e_3 - e_4): B-space is 4-dim (exact); for two rational rank-3 B the admissible cone V_B
      (all Z with <P_0, Z> level) is a union of 6 irreducible quadric cones of dim 3 in 4-dim spans, so it contains no 3-dim linear space:
      no 6-dim M.  General B: OPEN (symbolic run > 1 GB; to be reformulated / queued).  Cases (I), (alpha): not started.
 R12-2 [classification, 20.2] the 19 rows-team (6,3) spaces: 5 line-spanned (covered by the closed patterns), 11 = one R2/C2 block on a line
      pattern ((1|2,1)+R2 x4, (2,1|1)+C2, (1|3)+R2 x4, (1,1|2)+R2 x2) whose undeformed bases are NOT level (outside the deformation table),
      3 clm spaces with N pieces.  Exact families for these 14: OPEN.
 R12-3 [exact, 20.4-20.5] hit-free patterns: (3,1,1|1), (3,1,1,1|) and (2,2,2|) closed by rigorous orthogonality reductions + exact GBs;
      TMO pool verdicts: 3 more classes EMPTY.  Now 26 of 29 settled (25 empty: 21 by the split, (3,2,1|), (3,1,1|1), (3,1,1,1|), (2,2,2|) by reductions; + (1,1,1,1|1,1) certified); OPEN: (2,1,1,1|1) [class 1001],
      (2,2,1|1) [class 110] (Singular halts at 2 GB), (2,2,1,1|) (reduced to cases A/B, queued REG2-HAND2211).
 R12-4 [20.3] piece existence: trivial lemma dim P_kl >= 6 - dim pi_r(M) - dim pi_r'(M); census: holds non-trivially in 184/187 spaces.
 R12-5 [20.0] stale-output check: all exact drivers parse captured Singular stdout; polylib.run_msolve (modular only) fixed.
## RESULT ROUND 11 (reg2, 00:06-01:20 UTC; section 19)
 R11-1 [exact, 19.1] the (2,2|2) CONIC DOUBLE DEFORMATION IS TRIVIAL: det G(V0) = Q, det G(U) = 125 Q, <V0,U> = 0; on Q = 0 both skew maps land
      in V0 cap U, so M(t,t2) = M(0,0), a (2,2|2) member (DR22).  The double-deformation table is closed; REG2-CONIC-DD cancelled.
 R11-2 [exact, 19.4] (1,1,1|1,1,1) CLOSED: exact incidence split (calibrated): 476/512 incidence classes empty, the other 36 form one orbit and
      give ONE space up to symmetry, M111 = <e_0(0,0,0,1,-1), e_1(0,0,-2,1,1), e_2(0,-3,1,1,1), (1,1,-3,1)e_0, (1,-2,0,1)e_1, (1,0,0,-1)e_2>,
      level, dim T_1 = 9 (16x16 minor UNIT) => FO2 <= 8.
 R11-3 [exact, 19.5-19.6] the 29 census-"hit-free" line patterns: 21 EMPTY (exact incidence split) + (3,2,1|) EMPTY by hand;
      (1,1,1,1|1,1) is NOT empty: one orbit of incidence classes = a 1-parameter family (u0 perp u1 in {w_0 = w_1 = 0}), level, dim T_1 <= 9
      [exact, chart + point at infinity] => FO2 <= 8; 6 patterns partial (classes that hit the 90-120 s limit: queued REG2-INCPAT-TMO).
      "0 hits" in a numerical census does NOT mean empty.
 R11-4 [rigorous + numerical, 19.2] 3-dim row blocks: rank 3 <=> "R2 + R1 on the same row pair" (kernel w0 of the skew form, B w0 = mu n);
      SK2 forces rank <= 2 unless (alpha) all zeta constant, (I) zeta in <1,e_c> with n_c = 0, (II) zeta in <1,1_S>, |S| = 2, n ~ e_d - e_d';
      robust census: never rank 3.  Exact exclusion of (alpha), (I), (II): OPEN.
 R11-5 [statement, 19.3] FINITE MECHANISM LIST for PROOF-MAP leaf 11: conditional theorem "(BL) => M = Lin(M) + genuine parts of types
      R1/C1, R2/C2 (t J + phi), N, [R3 open]", the census of observed types, and the exact list of what remains ((BL); R3; phi != 0;
      certification of the N- and R1-type families incl. the 19 rows-team spaces; the remaining hit-free patterns).
 OPEN: (BL); R3 cases (alpha)/(I)/(II); the remaining hit-free patterns / TIMEOUT classes (19.6); exact families of N/R1 types.
## RESULT ROUND 10 (reg2, 23:05-00:10 UTC; section 18)
 R10-1 [exact, 18.1] (2,2|2) DOUBLE DEFORMATIONS at the special points: all SIX families ((row 0->1,2,3) + (col 0->1) at mu=(0,1,1,1),
      (row 0->1,2,3) + (col 0->2) at mu=(0,1,0,0); row 0->3 was missing in round 9) have FO2 <= 8: new lift_gram.py defo2= option, rank q >= 3
      on charts covering t != 0, dim T_1 <= 10 by minors, t = 0 / t2 = 0 = closed single deformations.  Logs r10_lift_double_*, r10_double_*.
 R10-2 [exact, 18.5] (2,1,1|2)(ii) (ii-g) ROW-DEFORMATION CURVES: CLOSED.  Homogeneous polynomial parametrisation over Q(w) (b on the
      isotropic conic, c rational in s); 16x16 minors leave 16 lines s = s0: 7 linear + 6 quadratic certified (UNIT or t = 0 only), 3 quadratic
      degenerate (b || c, dim 5, exact); s = infinity certified; the c0 = 0 chart scan has no further components; rel02 by the row swap.
      => dim T_1 <= 9, FO2 <= 8 on every (ii-g) row deformation.
 R10-3 [rigorous + exact, 18.2/18.4] LEMMA SK3: a FULL 4-dim row block P = {e_r w + e_j Bw : w in 1^perp} of a 6-dim level space has
      rank B <= 2.  Proof: B = K|W with K skew, K1 = 0; SK2 sharpens to [diag(zeta_Z), K] = 0 for every Z in M, so a non-constant zeta_Z
      forces K block diagonal => rank <= 2; if all zeta_Z are constant, Z has the shape a e_r 1 + b e_j 1 + e_k p + e_l(lam 1 - p), and these
      spaces DO NOT EXIST (Singular over Q, 4 echelon charts, UNIT even without the rank condition; validated + calibrated).  So a full free row
      admits only the standard 2-dim skew deformation (proves 17.5(b)).
 R10-4 [numerical, 18.7] automated non-skew filter: 840 cases, 12 hits, all decomposable, 0 genuine non-skew blocks (calibration 3/60 kept).
 R10-5 [evidence, 18.0] verify2's request: 102 cheap exact certificates of rounds 3-9 re-run with saved logs, reg2/evidence/logs/ (102/102 OK).
 TOOLS: lift_gram.py / omega_e0.py defo2=; gen_rank.py exact omega reduction + row-normalised greedy + reduction mod relations + num= on-locus
      points; gen_rank_defo.py fix=s:alpha+beta*w (18.3).
 OPEN: the CONIC double deformation of (2,2|2) (numerically (9,3,7); exact runs exceed 1 GB / 25 min -> QUEUE REG2-CONIC-DD); 3-dim row blocks
      (rank of the map B); (BL); (1,1,1|1,1,1) (not started).
## RESULT ROUND 9 (reg2, 22:47-23:04 UTC; section 17)
 R9-1 [exact, 17.2-17.3] (2,1,1|2)(ii): every SIGMA-curve column deformation (both parameter charts) and every (d)-component deformation
      (column deformations over Q(omega), row deformations over Q(i)) has FO2 <= 8 (new generic tool reg2/gb/lift_gram.py for rank q >= 3 +
      minors + exact leftover points; the uncovered points are degenerate (a = 0, not 6-dim) or certified exactly).
 R9-2 [exact, 17.6] double deformations over the (2,2|2) special points: dim T_1 <= 10 everywhere; rank q >= 3 not yet certified.
 R9-3 [rigorous, 17.5a] LEMMA SK2: on a skew two-row piece {e_r w + e_j Bw}, P_3 coupling with any Z forces (w,w') -> <w o zeta_Z, Bw'> to be
      skew (zeta_Z = sum of the other two rows of Z): B must commute with diag(zeta) modulo 1 -- the mechanism that cuts 4-dim row blocks down.
 R9-4 [numerical, 17.5b,c] skew deformations of a FULL FREE ROW exist only with rank B = 2 (20/20 solutions per case, 12 cases): a 4-dim skew row
      block never survives; these deformed Type F spaces have FO2 <= 8 (9 is lost). Non-skew two-column elements found so far are all
      decomposable (single-row element + skew block).
 OPEN: (2,1,1|2)(ii) row deformations on isotropic curves; rank q of the double deformations; the conic double deformation; a proof that
      non-skew blocks and 4-dim row blocks cannot occur (SK2 is the tool); (1,1,1|1,1,1).
## RESULT ROUND 8 (reg2, 22:32-22:48 UTC; section 16) -- the deformation table is closed except (2,1,1|2)(ii) and the double deformations
 R8-1 [exact, 16.2] all six LEVEL-FOR-ALL skew deformations have FO2 <= 8 for every member: four have dim T_1 <= 9 everywhere (new generic
      Omega/E_0 tool reg2/gb/omega_e0.py + minors on the uncovered loci), (2,2|2) row 0 -> 1 has two (10,4,8) curves (minors + gcd of minors),
      (2,2|1,1)BB rows were closed in round 7.
 R8-2 [exact, 16.6] every special-locus deformation over a POINT or a CONIC of the base family (27 rational points, 3 omega loci, 2 conics) has
      FO2 <= 8 (reg2/gb/certify_defo.py, gen_rank_defo.py with fixed base points / omega / on-locus minor selection).
 R8-3 [exact scan, 16.4] double deformations occur ONLY over the special points mu = (0,1,1,1), (0,1,0,0) and one conic of (2,2|2).
 R8-4 [rigorous, 16.5] LEMMA SK (why skew): on a two-column piece {x e_a + y e_b} of a level space, P_1 and P_2 give <x,y'> + <x',y> = -2(Sx)(Sx');
      so on its sum-zero part y = A x with A SKEW; a skew map on the 3-dim 1^perp has a kernel line, so a column block adds at most 2 dimensions
      beyond the line span (as observed); rank-one elements x (x) v with Sx = Sv = 0 need x or v isotropic.  Not proved: absence of other
      non-line pieces, i.e. (BL) and the multi-skew conjecture.
 OPEN: (2,1,1|2)(ii) deformations (SIGMA-curve column deformations need the rank certificate; row-deformation loci partly outside the family);
      double-deformation families; the rank-one mechanism; (1,1,1|1,1,1).
## RESULT ROUND 7 (reg2, 22:11-22:31 UTC; section 15) -- the bi-line spaces are SKEW DEFORMATIONS of line-spanned ones; a deformation table
 R7-1 [empirical + exact, 15.2-15.4] Every non-line-spanned space found arises from a line-spanned family by skew deformations: a 2-dim
      single-column part V (x) e_a becomes {x e_a + t (J_V x) e_b} (J_V the rotation of V; P_2 = t <x, J_V x> = 0), or the transposed row version.
      SYSTEMATIC SCAN (exact level ideals, reg2/gb/defo_scan.py): for all 15 closed line-spanned families with a 2-element single-line group, the
      loci admitting a level deformation are listed in 15.4 (5 families deform for all parameters, ~15 special loci, many pairs none).
 R7-2 [exact, 15.3] the (2,2|1,1)BB row deformations (row 0 -> 1, 2, 3; 2-parameter families, whole family (10,4,8)): FO2 bound <= 8 for every
      member (minors for dim T_1 <= 10, lifts + Gram minors for rank q >= 3, exact leftover points).
 R7-3 [exact, 15.6] TARGET 4: independent Omega/E_0 certificate of dim T_1 <= 10 on the whole (2,2|1,1)BB curve (no minors tool); together with
      the gcd-method rank check this is a complete second certificate of FO2 = 8 on BB.
 R7-4 [numerical, 15.5, 15.7] the five level-for-all deformations are (9,3,7); (BL) holds on 187 / 187 spaces; all 103 deletable-row hits FO2 <= 8.
 NOT DONE: exact certificates of the level-for-all deformations of (2,2|2), (2,1,1|2)(iii), (2,1|2,1)V0, (1,1,1|2,1)A1, (2,1|3) (3-parameter
      minor runs too slow -- use the Omega/E_0 pipeline next); the special-locus deformations; double deformations; a proof of (BL);
      (1,1,1|1,1,1) and the hit-free patterns.
## RESULT ROUND 6 (reg2, 21:57-22:10 UTC; section 14) -- "line-spanned" is FALSE; the empirical replacement (BL) holds on 147/147 spaces
 R6-1 [exact] A 2-parameter family of NON-line-spanned 6-dim level spaces with a deletable row (BLOCK family, 14.5):
      e_0 (x) {1,m}^perp (+) C e_2 m^T (+) {x e_1^T + a (Jx) e_4^T : x in V}, m = (t,0,-1-t,1,0), J = the rotation of V = {x_0 = 0, sum = 0};
      level for all (t,a); not line-spanned for a != 0; every level space containing a member has dim <= 8 (exact: lifts + minors; SP8 at the
      two-column values of m).
 R6-2 [exact] One more non-line-spanned space (RANK-ONE, 14.6) with isotropic m = (1,0,w^2,0,w): (10, 4, 8) over Q(sqrt -3).
 R6-3 [numerical] deletable-row census (reg2/dr35.py): u = 3: 24 hits / 250 (7 non-line-spanned, all of the two shapes above), u = 2: 5 / 250,
      u = 1: 1 / 200 (all line-spanned); every hit FO2 <= 8.  So the table must be extended by rank-one and skew-block elements; still no
      counterexample to (S6-FO2).
 R6-4 [tool fix] gen_rank.py now skips degenerate random points (it aborted when a random rational parameter hit 0).
 R6-5 [exact, 14.8] DOUBLE-BLOCK family (u = 2): S contains no line element at all; level for all (a,b); dim T_1 <= 10 and rank q >= 3 for
      every member, so FO2 bound <= 8 on the whole family.
 R6-6 [numerical, 14.10] STRUCTURE LAW (BL): all 155 six-dim 4x5 level spaces at hand (45 not line-spanned; 71 deletable-row hits + 84 others) are spanned by their elements
      supported in at most two rows or at most two columns. This is the proposed replacement for "line-spanned".
## RESULT ROUND 5 (reg2, 21:26-22:00 UTC; section 13) -- every line-spanned pattern with a census hit is now closed exactly; one tool bug fixed
 R5-1 [hand + EXACT, 13.1] (2,2|1,1): families BB (1 parameter, the whole curve has dim T_1 = 10: rank q >= 3 certified for every member by
      unique lifts + Gram minors, gb/p2211_rank.py) and BD (2 parameters, dim T_1 <= 9 except 8 points, seven of them (10, rank 4, 8));
      every member has FO2 bound <= 8. These are the census (3,10,8) hits.
 R5-2 [hand + EXACT, 13.3] (1,1,1,1|2): case B empty; case A main family via the Omega/E_0 pipeline (gb/gen_1111d.py): 48 Omega + 156 E_0 tests
      unit over Q (calibrations non-unit): dim T_1 <= 9 for every member, no special locus; degenerate sub-cases reduce to it or to one exact space.
 R5-3 [hand + EXACT, 13.4] (2,1|1,1,1): twelve type triples, nine empty by hand; ABD (one space), ACC, ACD (1 parameter each): dim T_1 <= 9.
 R5-4 [bug, 13.2] gen_rank.py / gen_rank2.py entered level equations without parentheses (Singular added them term by term). Only
      (1,1,1|2,1)B2 had level equations: recertified (12 leftover points, all dim T_1 = 9); the round-4 gen_rank2 inconsistency is explained.
 R5-5 [numerical, 13.11] CE-1 finished: 45 patterns x 200 starts, 1142 hits in 15 patterns, no candidate; NEW pattern (2,1,1|1,1).
      ALL 15 patterns with hits are now closed exactly (13.12).
 R5-6 [hand + EXACT, 13.9-13.10] (2,1,1|1,1) CLOSED: every member has FO2 bound <= 8, including the 2-parameter (3,10,8) family (a,a)
      (lifts + Gram minors), the isotropic sub-family IV-iso and the case-II family. Open among line-spanned patterns with members:
      only (1,1,1|1,1,1) (one hit in 20 starts in round 4, none in 460 later starts).
## RESULT ROUND 4 (reg2, 20:41-21:15 UTC; sections 10-12) -- EL refuted as a lemma; five more NC patterns closed exactly; census E calibrated
 R4-1 [rigorous + EXACT; 10.1] The law EL ("deletable row i, M = S (+) e_i (x) U  =>  Omega(M) inside A(U) = {s : U o s in U + C1}") is NOT a
      general lemma: hand counterexample M = C e_0 (e_1-e_2)^T (Omega = C^5, A = {s_1 = s_2}); exact counterexample to the SATURATED form
      (U = (C(S)+C1)^perp): (2,2|2) member mu = (0,1,2,3), S = C(B_0 + 2B_1 - B_4 + 3B_5), dim T_1 = 13, Omega = C^5, dim A(U) = 2 (reg2/el_exact.py).
      It holds (numerically) for every 2-, 3-dim S inside the DR families and for all 6-dim spaces, so any proof must use dimension 6.
      Useful reformulation [rigorous, 10(b)]: t in T_1 <=> (C0) and <u o rho, G(K)> = D_{X' - K D_rho} <u, G(K)> for u in U, K in J'_3 + S'.
 R4-2 [EXACT, char 0; section 11] dim T_1 <= 9 (so FO2 bound <= 8) for EVERY member of the NC patterns (3|2,1), (2,1|3), (3|1,1,1), (2,1|2,1),
      (1,1,1|2,1); hand case splits (several incidence cases EMPTY), level for all parameters except (1,1,1|2,1)(B2) (level variety: 3 curves).
      Method: K greedy 16x16 minors of the FO coefficient matrix over Q[params] (reg2/gb/gen_rank.py) generate (1), or cut out finitely many
      points, each certified exactly (reg2/nc_cert.py, Q or Q(sqrt -3)); complex-conjugate points by conjugation.
 R4-3 [numerical; section 12] census E (line-spanned, 45 patterns x 20 starts, calibrated on all 11 exactly known patterns): 104 hits,
      (2,9,7) x 102 and (3,10,8) x 2, no candidate; NEW patterns with members: (2,2|1,1), (1,1,1,1|2), (1,1,1|1,1,1) (and (2,1|1,1,1)).
      Full run (200 starts/pattern, 6 x 1 core, < 0.1 GB each) queued as CE-1 in /home/kevxhk/work/QUEUE.md.
 R4-4 [hand + partial; 11.7] (1,1,1,1|2): case B EMPTY (hand); case A = orthogonal frame (u_1,u_2,u_3) in H_4 with T = 0 plus u_0 = (1,1,1,1,-4)
      (the degenerate sub-cases reduce to it or to one space, exact over Q(i): dim T_1 = 9); the main family is (2,9,7) NUMERICALLY, its exact
      certificate is NOT finished (inconsistent minor run, 11.7).  Open line-spanned patterns: (2,1|1,1,1), (2,2|1,1), (1,1,1,1|2)(A), (1,1,1|1,1,1).
 THEOREMS OF ROUND 3 (for the audit; inputs = scripts + logs named in section 9):
   DR211-i   [hand, 9.1]  case (i) of (2,1,1|2) has no 6-dim level member.
   DR211-ii  [exact, 9.4] for every ([a],[b],[c]) in H^3 pairwise orthogonal with T(a,b,c) = 0: dim E_0 = 7; dim Omega = 2 off SIGMA u D; on SIGMA u D
             dim T_1 = 10 and rank q >= 3.  Inputs: gen_dr211d.py + dr211_common.py (Singular over Q: 48 Omega eliminations, 156 E_0 std; logs
             gb/runs/dr211q.log, dr211q_ge0.log; minimal primes gb/minass_q.py), gen_s4.py (SIGMA_4 Omega test), dr211_special.py (S4 symbolic, D,
             S4pt, pt at s = +-1).
   DR211-iii [exact, 9.6] case (iii): dim T_1 <= 9 for every member (gen_dr211.py modes elim, e0; log gb/runs/dr211iii.log).
   P312      [hand + exact, 9.7] (3,1|2): every level space containing a member has dim <= 8 (gen_p312.py om/e0, log gb/runs/p312.log;
             p312_special.py for m = (1,w,w^2,0,0); SP8 for non-isotropic / two-column m).
   P3111     [hand + exact, 9.8, 9.11] (3,1|1,1): same conclusion (gen_p311.py logs gb/runs/p311*.log; p311_rank.py Bpt; gb/p311A_rank.py, log
             gb/runs/p311A_rank.log).
   P33       [exact, 9.9] (3|3): (9, 2, 3, 7) (p33_cert.py).
## RESULT ROUND 3 (reg2, 19:45-20:45 UTC; details in section 9) -- REG2-T1 DECIDED; three more line-spanned patterns closed
 R3-1 [EXACT, char 0 + hand; 9.1-9.6] THE SUPPORT PATTERN (2,1,1|2) SATISFIES (S6-FO2).  Case (i) is EMPTY (hand: forces b ~ (1,i,-1,-i) and a
      contradiction). Case (ii) (the undecided one) = {a,b,c in H pairwise orthogonal, sum a_j b_j c_j = 0}, a 2-dim variety: for EVERY member
      dim E_0 = 7, and dim Omega = 2 (dim T_1 = 9, FO2 <= 8) except on the curves SIGMA_k (b, c share a zero column; a ~ 1 - 4e_k) and the orbit D
      (b, c = disjoint two-column vectors), where dim T_1 = 10, rank q >= 3, FO2 bound = 8 [Singular over Q, 48 + 156 chart systems, cross-checked mod p
      by msolve; symbolic analysis of SIGMA_4 over Q(s); exact rational certificates at the special points]. Case (iii): dim T_1 <= 9 for every member
      [Singular over Q]. Explanation: the jump locus is exactly where a is two-valued, i.e. where A(U_0) = {s : U_0 o s in U_0 + C1} is 3-dim (law EL).
 R3-2 [EXACT; 9.7] pattern (3,1|2): level for every m with m_c = 0 (hand); dim T_1 = 9 unless |supp m| <= 3; the only ISOTROPIC special member
      m = (1,w,w^2,0,0) has (dim T_1, rank, FO2) = (10, 4, 8) over Q(sqrt -3). Non-isotropic / two-column m: SP8. So every level space containing a
      (3,1|2) member has dim <= 8 -- including the isotropic m that SP8 cannot reach.
 R3-3 [EXACT; 9.8, 9.11] pattern (3,1|1,1): every level space containing a member has dim <= 8. Non-isotropic / two-column m: SP8. Isotropic m:
      sub-case (B) dim T_1 = 9 except one orbit (exact (10,4,8) over Q(sqrt -3)); sub-case (A) (m = (1,w,w^2,0,0), one-parameter x): dim T_1 <= 10 and
      rank q >= 3 for EVERY member (Singular over Q with w^2+w+1 = 0: explicit unique lifts of rho = e_3, e_4, Gram matrix of q on
      span(d_0, tau, t_3, t_4), ideal of its 3x3 minors = (1) on every chart), so FO2 bound <= 8.
 R3-4 [EXACT; 9.9] pattern (3|3) is a single space, (9, 2, 3, 7).
 Not done this round: the NC patterns (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1), (1,1,1|2,1); target 2 (structure theorem) beyond the
      observed EL mechanism; census E (needs the 24-core queue, see COMPUTE-reg2.md section 8).
## RESULT ROUND 2 (reg2, 19:59 - 21:xx; details in sections 5 - 8) -- the regime is NOT closed; four new rigorous pieces
 R2-1 [RIGOROUS, hand; section 5] THEOREM SP8: a level space of 5x5 matrices containing e_i (x) {w : sum w = 0, <m,w> = 0} has dim <= 8 if
      m = e_a - e_b, or if <m,m> != 0 and it contains e_i' m^T for another row i'. (stage2's (Z3): L_i is a 4x5 level space with defect in C m;
      then verifyfl's TC5 / SPLIT / SL.) This excludes, for ALL parameters and without computation, the families that defeated the
      first-order criterion: M*_1(x,y), M*_2, every single EC move of a Type F space, and the DR3 spaces with their split element.
 R2-2 [RIGOROUS; 8.1] (a) FO2 bound(M) <= dim T_1(M) - 1 for every M (q_0 = 12 P_2 is nonzero on tau_r in T_1(M)); so dim T_1(M) <= 9 implies
      (S6-FO2) for M. (b) (S6-FO2) + FL exclude a_r = 3 as well as a_r = 2 (6-dim subspace of L_r) -- as verify2 noted.
 R2-3 [EXACT, char 0, all charts, calibrations non-unit; 8.2, 8.3] with Singular / msolve in this container:
      NC family M(w0,w1,w3) (pattern (1,1,1|3)): Omega = span(1,e_0), E_0 = M + C d, dim T_1 = 9 for EVERY member;
      the WHOLE support pattern (2,2|2) (a new explicit 2-parameter family M(mu), level for every mu): dim T_1 = 9 except at the 0/1
      vectors mu, where (dim T_1, dim Omega, rank q) = (10, 3, 4). So (S6-FO2) holds on both (every level space containing a member has
      dim <= 8; dim <= 7 if it is L_r and mu is not 0/1), and all these spaces are maximal 4x5 level spaces.
 R2-4 [RIGOROUS; 7.1-7.3] Lemma DL / Proposition MAX: row i deletable <=> (e_i - 1/4) (x) 1 in E_0(M); neutral column c => 1 (x) (e_c - 1/5)
      in E_0(M); P_2 = -15/2, -24/5 on these directions; so a space with a deletable row or neutral column and dim E_0 = dim M + 1 is
      maximal. Hence "every 6-dim 4x5 level space has a deletable row or neutral column and dim E_0 = 7" would give "4x5 level <= 6".
 R2-5 [section 6] FILTER for regime 1: a row with a_r = 1 needs Phi = 0 and Omega(L_r) = C^5 (one SVD). Generic hyperplanes of the Type F
      spaces with Omega = C^5 pass it (and FO2 = 9): by (Z3) they are regime-1 candidates exactly if a (5,1) space with a generic line
      exists. Hyperplanes of M* fail it or are excluded by SP8.
 STATUS OF "L_r = M (dim 6) inside a 9-dim level space", by family:   F: FL [rigorous];   M*, EC moves, DR3-split: SP8 [rigorous];
      pattern (2,2|2), NC family (1,1,1|3): [exact];   other NC / DR2 spaces: criterion A with Omega computed per space [numerical];
      DR3 with isotropic or non-split m: none found; reduces to "(5,1) with that line".
 NOT DONE: target (1) "6-dim => deletable row or column" (no proof; upstream L_gct_215 has no dim-6/7 structure statements beyond the
      case tree, see 7.4); target (3) reduced to (1) + dim E_0 = 7 (7.3) or to (S6-FO2) (8.1(b)); no 7-dim space found.
 EMPIRICAL LAW (EL) [numerical, 7.5]: Omega(M) lies in {s : U_i o s inside U_i + C1} for every single-row part of a 6-dim M (55 rows, 0
      violations); if true for L_r in regime a_r = 2 it forces every single-row element outside row r to be a multiple of e_i (e_a - e_b)^T.
 Best next steps: TASK X1 of COMPUTE-reg2.md section 7 (exact treatment of the remaining line-spanned patterns; each run is seconds with
      reg2/gb/famtool.py), a proof of (EL), and the classification (1).

## RESULT (reg2, final 19:55) -- regime a_r >= 2 NOT closed by a proof. New: a rigorous first-order criterion, the taxonomy of 6-dim 4x5
## level spaces (four families, one of them NEW and exact), and the exact statement that would close the regime.
 Notation: L level 5x5, row r, M := L_r (4x5 level, dim 4 + a_r if dim L = 9), W_r := row-r projection of L, J' = 4x5 all-ones,
 N_j(X) = perm_4(X without column j), F = sum_j N_j, C(M) = defect space (rows), e = dim C(M), Phi(Y) = N(Y),
 T_1(M) = stage2's first-order space (M placed in the rows != r), Omega(M) := row-r projection of T_1(M)  (a subspace of C^5).
 A [RIGOROUS, section 1] FIRST-ORDER + FK CRITERION (new):  tau_r := J - 5 e_r 1^T lies in T_1(M) for EVERY level M, so 1 is in Omega(M);
    W_r lies in Omega(M) and never contains 1 (FK). Hence for every level space L and every row r
          dim L  =  dim L_r + dim W_r  <=  dim L_r + dim Omega(L_r) - 1,      dim Omega(M) = (4 - e(M)) + g(M),  1 <= g(M) <= e(M) + 1
    (g = number of independent defect functions <v, N(J'+Y)> of M that are first-order level variations D_X F(J'+Y); g = 1:
    dim L <= dim L_r + 4 - e(L_r), rows' defect bound WITHOUT assuming row r deletable). Also rigorous: Phi(L_r) lies in
    (row-r projection of L^)^perp (dim a_r - 1); Omega(M) is orthogonal to Phi(M);
          Omega(M) = { s in C^5 : the function Y -> D_{Y D_s} F(J'+Y) on M is of the form Y -> D_X F(J'+Y) }      (D_s = diag(s)),
    i.e. Omega = infinitesimal COLUMN scalings keeping M level to first order up to a translation. Checked on 70 lines of the 7
    known spaces: no violation, equality in 39 (reg2/chk_lemma.py). For a 9-dim L: a_r = 2 needs dim Omega(L_r) >= 4.
 B [NUMERICAL + EXACT examples; sections 2, 4] THE KEY QUESTION "does every 6-dim 4x5 level space contain a full free line?": NO.
    Every 6-dim 4x5 level space found (about 200, from five differently biased searches) has a DELETABLE row or column and
    falls into one of four families, with invariants (dim Omega, dim T_1, FO2 bound):
      F    full free row e_i (x) 1^perp (+) 2-dim, e = 4:                         (3,10,8) [rc45] or (5,12,9) [kernels of L080, ex2, ex3, ...]
      NC   one neutral column c, e = 3, Omega = span(1,e_c) (19 files of rows):   (2, 9,7)
      DR2/DR3  deletable row with free part of dim 2 or 3, e = 4, no neutral column, no full free row (NEW here):
               (2,9,7), or (3,10,8) with Omega = indicators of a column partition {a},{b},{rest} (rc45-like), or
      M*   (4,11,8):  the EXACT family  M*(x,y) = e_3 (x) {w : sum w = 0, w_1 = w_2} (+) C x e_0^T (+) C y e_3^T (+) C e_2 (e_1-e_2)^T,
               x, y in C^3 (rows 0,1,2), sum x = sum y = 0, <x,y> = 0 (e.g. x = (1,-1,0), y = (1,1,-2)): 6-dim, level (hand proof,
               section 4), NO full free row, Phi = 0, Omega(M*) = (e_1 - e_2)^perp of dimension 4, dim T_1 = 11.
    So "(S6') dim Omega <= 2 (or <= 3) without a full free row" is FALSE: M* passes EVERY first-order necessary condition for being
    L_r of a 9-dim level space with a_r = 2 (R_r = k^perp, k = e_1 - e_2, Phi = 0). It is excluded only at SECOND order:
    EXACT (rational arithmetic, reg2/mstar2_fo2.py): dim ker = 11, rank of q_Y on it = 5, so every level space containing M* has
    dim <= 8. Numerically M* lies in 7-dim level spaces (9 of 12 starts) but in no 8-dim one (0 of 70 starts, 6 unknowns).
    The Type F spaces with Omega = C^5 have FO2 bound 9: for them only Theorem FL (dim <= 7) works.
    All 41 spaces of rows / of the 7-dim examples are maximal 4x5 level spaces (E_0 = M + C d, P_2(d) != 0); 7-dim search through
    45 known smaller level spaces: 0 of 132 starts. No 7-dim 4x5 level space is known.
 C [CONSEQUENCE, rigorous given FL and stage2's Lemma FO2] a_r = 2 is impossible at dim 9 as soon as
      (S6-FO2)  every 6-dim 4x5 level space M without a full free row has FO2 bound <= 8
    (true for every space found: bounds 7, 7, 8, 8). a_r = 3 is impossible as soon as no 7-dim 4x5 level space exists, or every
    7-dim one has FO2 bound <= 8 (it contains no full free row by rows' SL_3 corollary). Both are statements about 4x5 matrices.
 D [NOT DONE] no proof of (S6-FO2); no classification of the 6-dim spaces ("deletable line" is the 4x5 analogue of conjecture (D));
    no proof of "4x5 level <= 6". The first-order criterion alone cannot close the regime (M*).
 Best next steps: (1) census of 6-dim 4x5 level spaces with dim Omega >= 4 and no full free row, with the FO2 bound of each
    (COMPUTE-reg2.md, sections 1-3b; the equal-column extensions of 5-dim equal-column spaces are the place to look: M* is one);
    (2) prove "6-dim 4x5 level => deletable row or column" along upstream L_gct_215's case tree; (3) for REGIME 1 the criterion
    gives the cheap filter Omega(L_r) = C^5; hyperplanes of the F spaces with Omega = C^5 and of M*-like spaces are candidates there.
STATUS 18:53: BRIEF + rows/stage2/chief notes read. First facts (numerical, reg2/t.py, a1.py, a2.py):
 - the "key question" has answer NO: rc45 contains a full free row, but the 19 (6,3) spaces of rows (clm_p4_d6_defect3_*, nc_d6_k1_*,
   seed_d6_e3_*) contain NO full free row (single-row parts of dim <= 2) and no full free column. All 19 have dim T_1 = 9, rank q = 3,
   FO2 bound 7; rc45: T_1 = 10, rank 4, FO2 bound 8 (and <= 7 by FL).
 - rigorous remark (Z2 weak form, 2 lines): for u in L^ and Y in L_r, s^4-coefficient of perm(u + sY): <u_r, Phi(Y)> = 0, Phi(Y)_j =
   perm_4(Y without column j). So Phi(L_r) lies in R_r^perp (dim a_r - 1): for a_r = 2, Phi(Y) = phi(Y) k for ONE vector k (sum k = 0).
   Among the 19 spaces only some have rank Phi <= 1 (rc45, seed t4/t9: Phi = 0; nc s2, s23: rank 1).
STATUS 19:10: (1) the LM (6,3) files are 1e-7-close to SPARSE limit spaces (rounded rref, level error 1e-12): all 15 clean limits are
 spanned largely by single-row and single-column elements (e.g. nc_d6_k1_s23 = full free column of the 4 rows (+) three single-row
 elements; seed_d6_e3_t4 = e_1 (x) 3-dim (+) three single-column elements); none has a full free row except rc45. Row-projection
 ranks of the limits: (3,3,3,3), (2,2,1,2), (3,2,3,2), ... so "some row projection >= 4" is NOT a general property.
 (2) NEW first-order criterion (rigorous; see section 2): Omega(M) := row-r projection of T_1(M) contains 1 (tau_r = J - 5 e_r 1^T is
 always in T_1(M)), while the row projection W_r of a level L never contains 1 (FK). Hence for L_r = M: dim L - dim M = dim W_r <=
 dim Omega(M) - 1. Data: all 19 (6,3) spaces have dim Omega = 2 (so L_r = M forces dim L <= 7), rc45 has Omega = span(e_4, e_0+e_1,
 e_2+e_3) (dim 3; dim L <= 8, and <= 7 by FL). So none of the 20 known 6-dim 4x5 level spaces can be L_r of a 9-dim level space,
 already at first order. Target now: prove dim Omega(M) <= 3 for every 6-dim level M (would close a_r = 2), or find a counterexample.
STATUS 19:18: (a) COUNTEREXAMPLES to "dim Omega <= 3 for all 6-dim M": the 6-dim line-kernels of L080 (columns 0-3), ex2, ex3, fam2,
 s-family (row 4) have Omega = C^5, dim T_1 = 12, FO2 bound 9 -- but all of these contain a FULL FREE ROW (Type F: free row (+) 2-dim),
 so FL applies. All other known 6-dim spaces (Type NC: exactly one neutral column c, e = 3, C(M) = e_c^perp cap 1^perp) have
 Omega = span(1, e_c), dim T_1 = 9, FO2 = 7. (b) every known 6-dim M has E_0(M) = M (+) C d with P_2(d) != 0: maximal 4x5 level
 spaces. (c) reg2/ext6.py: ALL 6-dim level extensions of 16 known 4- and 5-dim level spaces (search inside E_0(M_b)/M_b, 2-10
 unknowns): 60 new 6-dim spaces, every one of Type NC. Writing up: regime a_r >= 2 is closed by FL + (S6'): "a 6-dim 4x5 level
 space without a full free row has dim Omega <= 2" (first-order statement about 4x5 spaces).
STATUS 19:30: COMPUTE-reg2.md written (heavy computations for the 24-core machine: censuses A-D, exact items). Exact Type NC family
 found and hand-proved (section 2.5, reg2/fam_nc.py). Writing sections 1-3.

## 1. Rigorous statements (hand proofs; all checked numerically by reg2/chk_lemma.py: 70 lines of the 7 known spaces)
 Setting: M a 4x5 level space, embedded in 5x5 matrices with zero row r (write t = (X ; rho), X = the rows != r, rho = row r).
 perm(J + (X;rho)) = sum_j (1 + rho_j) N_j(J' + X)  (Laplace along row r), N(J') = 24*1, F = <1, N>.
 gamma(v) := the function Y -> <v, N(J'+Y)> on M (v in C^5);  delta(X) := the function Y -> D_X F(J'+Y) on M (X in C^{4x5}).
 L1 (structure of T_1). (a) T_1(M) = {(X;rho) : gamma(rho) + delta(X) = 0}.  (b) ker gamma = Z(M) := (C(M) + C1)^perp (dim 4 - e),
    im gamma has dim e + 1 and contains the constants (gamma(1) = 120).  (c) ker delta = E_0(M), and delta(J') = 480
    [F(c(J'+Y')) = 120 c^4 and D_Y F(J'+Y') = 0 for Y, Y' in M give D_{J'} F(J'+Y') = 480].  (d) Hence tau_r := (J' ; -4*1) =
    J - 5 e_r 1^T lies in T_1(M), Omega(M) := {rho : exists X, (X;rho) in T_1(M)} contains 1 and Z(M), and
         dim T_1(M) = dim E_0(M) + dim Omega(M),   dim Omega(M) = (4 - e) + g,  g := dim(im gamma cap im delta), 1 <= g <= e + 1.
    Proof: (a) is the derivative of the Laplace expansion; (b): span{N(J'+Y)} = C1 (+) C(M); the rest is linear algebra.  QED
 L2 (degree splitting). (X;rho) in T_1(M) iff for all Y in M:  <X, grad P_{k+1}(Y)> + <rho, p_k(Y)> = 0 (k = 0..3) and
    <rho, Phi(Y)> = 0, where P_k are the 4x5 subpermanent sums, p_k(Y)_j = P_k(Y without column j), Phi = p_4, and
    p_k(Y) = colsum(grad P_{k+1}(Y)) / (4 - k) for k <= 3.  [D_t P^{5x5}_{k+1}((Y;0)) = 0 for each k by homogeneity; the (i,j)
    entry of the gradient is P_k of the minor.]  So Omega(M) is orthogonal to Phi(M), and with G_k := span{grad P_{k+1}(Y)}:
    Omega(M)^perp = span Phi(M) + { sum_k colsum(V_k)/(4-k) : V_k in G_k, sum_k V_k = 0 }  (relations among G_0..G_3).
 L3 (column scalings). For every 4x5 X and s in C^5:  <s, N(X)> = (sum s) F(X) - D_{X D_s} F(X), D_s = diag(s) acting on columns
    [perm((X;rho) D) = det(D) perm(X;rho), differentiate at D = 1, rho = 1]. Hence
         Omega(M) = { s : the function Y -> D_{Y D_s} F(J'+Y) on M lies in im delta },
    in particular Omega(M) contains every s with M D_s inside M. Euler form: s in Omega iff there is X with, for all Y in M,
      (D1) 4 <s, colsum Y> = D_X P_2(Y);  (D2) 3 E_s P_2(Y) = D_X P_3(Y);  (D3) 2 E_s P_3(Y) = D_X P_4(Y);  (D4) E_s P_4(Y) = 0,
    E_s P_k(Y) := sum over k-subsets S of columns of (sum_{c in S} s_c) * (sum of the k x k subpermanents of Y in columns S).
    (Row scalings give nothing: D_{D_x Y} F(J'+Y) = 120 sum x - D_{x 1^T} F(J'+Y) is always in im delta.)
 L4 (CRITERION). Let L be a level space of 5x5 matrices, r a row, M := L_r, W_r := row-r projection of L. Then
      (i) L lies in T_1(M) (stage2's FO), so W_r lies in Omega(M);  (ii) dim L = dim M + dim W_r;  (iii) 1 is not in W_r
      (if t_r = c 1, c != 0, then J - t/c has a zero row: perm = 0 != 120);  (iv) 1 is in Omega(M) (L1).
    Therefore  dim L <= dim L_r + dim Omega(L_r) - 1 = dim L_r + 3 - e(L_r) + g(L_r).   QED
    Remarks. g = 1 ("untwisted"): dim L <= dim L_r + 4 - e(L_r), the bound of rows' defect construction, now for EVERY row
    (deletable or not). The criterion uses no second-order information; it is sharp on 39 of the 70 lines of the known spaces.
 L5 (Phi). For u in L^ = CJ + L and Y in L_r the s^4-coefficient of perm(u + sY) is <u_r, Phi(Y)>, so Phi(L_r) is orthogonal to
    R_r := row-r projection of L^ (dim 6 - a_r): for a_r = 2, Phi(Y) = phi(Y) k with one vector k, R_r = k^perp, sum k = 0.
    More generally for u = (X;rho) in L^, Y in L_r: sum_j rho_j N_j(X + Y) = 120 ell(u)^5 does not depend on Y; its parts of
    Y-degree 4, 3, 2, 1 are the exact (not only first-order) conditions; for rho zero-free it says that the column-rescaled
    space M D_rho^{-1} is "level at the base point X D_rho^{-1}" (F(X D^{-1} + Y D^{-1}) constant) -- a 4-parameter family of
    such rescalings when a_r = 2.
 L6 (pairs, consistent with chief's C8; rigorous). a_r = 2 (R_r = k^perp), a_i = 1 (ell = <n_i, u_i>), T = {j,l} with
    (k_j,k_l) != 0: on U_T = {u in L^ : u_r, u_i supported in T} row r is c (k_l e_j - k_j e_l), so perm_2 = c (k_l b - k_j a)
    ((a,b) = u_i on T) and ell = c lam_T. If ell != 0 on U_T (case B1) then k_l b - k_j a is proportional to ell, hence either
    n_ij k_l + n_il k_j = 0 or the image of U_T in the 2x2 block is ONE-dimensional and dim L_{ri} >= dim U_T - 1 >= 3.
    (No contradiction comes out: 6-dim spaces with all row projections of dim <= 3 exist, section 2.2.)

## 2. Data (numerical unless said otherwise; scripts in reg2/)
 2.1 The files of rows (rc45, clm_p4_d6_defect3_*, nc_d6_k1_*, seed_d6_e3_*; a2.py, a5.py, a6.py, a8.py). The LM files are within
     1e-7 of SPARSE limit spaces (rounded rref still level to 1e-12); invariants of the limits:
       rc45: single-row parts (0,0,0,4): full free row; e = 4; Phi = 0; dim E_0 = 7; dim T_1 = 10; Omega = span(e_4, e_0+e_1, e_2+e_3);
             FO2 bound 8 (FL: 7). The extra first-order directions are block means x (x) 1_C, C in {01}, {23}, {4}.
       the 19 others: no full free row (single-row parts <= 3), e = 3, exactly one neutral column c, Omega = span(1, e_c),
             dim E_0 = 7, dim T_1 = 9, rank 3, FO2 bound 7. Examples of limits: nc_d6_k1_s23 = {x e_0^T} (+) three single-row
             elements (section 2.5); seed_d6_e3_t4 = e_1 (x) (3-dim) (+) three single-column elements; nc_d6_k1_s4: row-projection
             ranks (3,3,3,3). Phi-rank 0, 1 or 2.
 2.2 Line-kernels of the 7 known 7-dim spaces (a10.py, a12.py): the 21 six-dim kernels are Type F (rows/columns: L080 columns 0-3,
     ex1/ex2/ex3/fam2/s-family row 4; Omega = C^5, dim T_1 = 12, rank 6, FO2 bound 9, except ex1 = rc45) or Type NC (L080 rows
     0-3, ex2 columns 2,3, ex3 columns 0,1, ...; Omega = span(1,e_c), T_1 = 9, FO2 = 7). So FO2 alone does NOT exclude dim 9 for the
     Type F kernels with Omega = C^5; FL does.
 2.3 Extension censuses (ext6.py, ext6c.py; every 6-dim level space containing M_b lies in E_0(M_b)): from 16 bases of dim 4, 5
     (60 solutions, all NC), from random 2-,3-dim subspaces of 8 six-dim spaces (61 solutions: the space itself, F or NC), from
     the 3-,4-dim line-kernels (25 solutions: 17 F, 8 NC). No space of another type. (Early "OTHER" labels were tolerance
     artefacts of singular convergence: defect singular values 1e-5; with relative tolerance 1e-4 they are NC or the F seed.)
 2.4 Maximality (a13.py): for all 41 spaces of 2.1-2.2, E_0(M) = M (+) C d with d a row-mean direction x (x) 1 (Type F) or a
     column-mean direction 1 (x) (5 e_c - 1) (Type NC), and P_2(d) != 0: none lies in a 7-dim 4x5 level space.
     5-dim census (ext5.py, 53 spaces): dim Omega in {2,3,4,5}; Omega = C^5 with Phi = 0 occurs with a full free row (9 times) and
     once without (a space with a full free column of its 4 rows) -- relevant for REGIME 1 only.
 2.5 EXACT Type NC family [hand proof]. w0, w1, w3 in C^4 (placed in columns 1..4) with sum w_i = 0, <w_i,w_j> = 0 (i != j),
     sum_c w0_c w1_c w3_c = 0;  M := {x e_0^T : sum x = 0} (+) C e_0 w0^T (+) C e_1 w1^T (+) C e_3 w3^T (dim 6 if all w_i != 0).
     Proof of level: expand F(J'+Y) along column 0: F = N_0 + sum_i (1 + x_i) n_i, n_i := sum over injections of the rows != i
     into columns 1..4. Rows are 1 + a_i w_i (i = 0,1,3) and 1 (i = 2). For rows with zero sums a 3x4 injection sum is
     24 - 2 sum_{pairs}<.,.> + (triple term), the triple term being 2 sum_c of the triple product when the pairwise dot products
     vanish; so n_0 = n_1 = n_3 = 24 (one of the three rows is 1), n_2 = 24 + 2 a_0 a_1 a_3 sum_c w0_c w1_c w3_c = 24, and
     N_0 = perm_4 with a row of ones = n_2 = 24. Hence F = 24 + 96 + 24 sum x_i = 120, and N_0 = 24: column 0 is neutral. QED
     Member w0 = (1,-1,0,0), w1 = (0,0,1,-1), w3 = (1,1,-1,-1): exact rational check of level; e = 3, dim T_1 = 9,
     Omega = span(1, e_0), FO2 bound (9,3) -> 7 (fam_nc.py).

## 3. What the regime a_r >= 2 now needs   [WRITTEN 19:30 -- SUPERSEDED by section 4 and by the RESULT block: (S6') is FALSE (family M*);
##    the statement to prove is (S6-FO2). Sections 2.1-2.5 remain correct as data; the F / NC dichotomy of 2.3 is incomplete.]
 (S6') every 6-dim 4x5 level space without a full free row has dim Omega <= 2.   Then (RESULT C) no 9-dim level space has a row or
 column with a_r >= 2, and more: dim L_r >= 6 implies dim L <= dim L_r + 1.
 Suggested split: (i) [structure] a 6-dim 4x5 level space has a full free row or a neutral column c with C(M) = e_c^perp cap 1^perp
 (then M = transposed defect extension of the 4x4 level space M^(c) of type (d',e') in {(3,0),(4,1),(5,2)}: the extremal cases of
 the 4x4 defect inequality); (ii) [no twist] for such M, im gamma cap im delta = constants. In the language of L2: the defect
 vectors p_k(Y) (k = 1,2,3) must all be weighted column sums of relations among G_0..G_3; in the language of L3: no column scaling
 other than span(1, e_c) preserves levelness of M to first order.
 Weak form sufficient for a_r = 2 alone: "dim Omega <= 3 without a full free row". For a_r = 3 alternatively: "no 7-dim 4x5 level
 space" (all 41 known 6-dim spaces are maximal).
 Files: reg2/{t,a1,a2,a5,a6,a7,a8,a9,a10,a11,a12,a13,show}.py (invariants), ext6.py, ext6b.py, ext6c.py, ext5.py (censuses),
 fam_nc.py (exact family), chk_lemma.py (sanity of section 1), M_L080_col0.npy, M_ex2_row4.npy (Type F with Omega = C^5),
 ext_*.npy (new NC spaces). Heavy-computation plan: COMPUTE-reg2.md.
STATUS 19:40: exact certificates (exact_T1.py) and the 7-dim extension search (ext7.py) added; RESULT block final. Remaining budget
 used for one more attempt on (ii) "neutral column => no twisted extension" (lead below).
STATUS 19:50: CORRECTION of the 19:18-19:40 picture. Two new censuses not seeded from known spaces (reg2/linespan.py: spaces spanned by
 single-row and single-column elements, 45 support patterns; reg2/drsearch.py: deletable row with free part of dim u) found
 6-dim level spaces OUTSIDE Types F / NC, among them the exact family M* with dim Omega = 4. (S6') is false. RESULT rewritten.

## 4. Deletable-row families and M* (found 19:40-19:50)
 4.1 linespan.py (M = sum of single-row parts e_i (x) U_i and single-column parts V_c (x) e_c, dims (u_i), (v_c), total 6; 45 patterns,
     2 starts each, two seeds): solutions for 12 patterns; NC for (3,0,0,0|3), (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1),
     (1,1,1|3), (1,1,1|2,1); and a type with e = 4, NO neutral column, Omega = span(1, e_c), (2,9,7), for (2,2|2), (2,1,1|2),
     (3,1|2), (3,1|1,1): there one row i meets M only in its single-row part (M = e_i (x) U (+) M_i, a deletable row with free
     part U of dim 2 or 3; rows' L(L'') spaces built from 3x5 spaces are of this kind).
 4.2 drsearch.py u (M = e_3 (x) U (+) N, dim U = u, N in rows 0-2 arbitrary): u = 3: 4 solutions in 25 starts: three with
     (dim Omega, T_1, FO2) = (3,10,8), Omega = span(e_a, e_b, 1 - e_a - e_b), single-row part of row 3 exactly 3-dim; one whose sparse
     limit is M* (4,11,8). u = 2: 1 solution in 4 starts (not analysed).  Each (3,10,8) space lies in 7-dim level spaces but in no
     8-dim one (reg2/ext55.py: 0 of 12 starts each, Gr(2,4)), like rc45.
 4.3 THE FAMILY M*(x,y) [exact; hand proof of level]. U := {w : sum w = 0, w_1 = w_2}; x, y in C^3 with sum x = sum y = 0, <x,y> = 0.
     M_0 := e_3 (x) U (+) C x e_0^T (+) C y e_3^T has equal columns 1 and 2 and is level: P_1 clear; P_2: the pairings are
     -<x,y> = 0, w_0 x_3 = 0 (x has no row 3), P_2(x e_0^T) = 0; P_3: only the triple (w, x, y) contributes,
     (sum_{i != i'} x_i y_i')(sum_{j != 0,3} w_j) = -<x,y>(...) = 0; P_4 = 0 because three of the rows 0,1,2 would have to use the two
     columns 0, 3. By rows' Lemma EC (equal columns 1, 2) M* := M_0 (+) C e_2 (e_1 - e_2)^T is level. dim M* = 6; row 3 carries only U.
     Exact rational member x = (1,-1,0), y = (1,1,-2) (reg2/mstar2.py, Mstar2.npy): level at 320 integer points, rank_Q of the gradient
     span = 14, dim T_1 = 11, Omega^perp = C(e_1 - e_2), e = 4, Phi = 0; FO2: exact rank 5 on the 11-dim kernel => dim <= 8.
     Other members ((2,-1,-1),(0,1,-1)); x = y = (1,w,w^2); ((1,2,-3),(5,-4,-1)): same invariants (11, 4, 8) numerically.
     Why Omega is large: U o s lies in U + C1 for every s constant on {1,2} (a 4-dim algebra), and the three other generators are
     single-line or equal-column elements. Extensions (ext55.py, ext55b.py): 7-dim level spaces M* (+) C t exist (9 of 12 starts,
     row-r rank 1); 8-dim: 0 of 82 starts (2-planes in the 5-dim T_1/M*).
     Meaning: M* is the first 6-dim space without a full free row that is first-order admissible as L_r for a_r = 2; any proof of
     the regime must use second-order (P_2-type isotropy) information or FL-type arguments, not only T_1.
 4.4 EC MOVES (reg2/ecmove.py; level by rows' Lemma EC; numerical invariants). For a Type F space e_3 (x) 1^perp (+) N whose N has two
     equal columns a, b, replace the free-row direction e_3 (e_a - e_b)^T by e_i (e_a - e_b)^T, i in {0,1,2}. All 30 spaces built
     this way (N = {x e_4^T : sum x = 0}: six pairs (a,b); N = C x e_0^T + C y e_3^T: three pairs; i = 0, 2) are 6-dim, level, without
     full free row, e = 4, and have (dim Omega, dim T_1, FO2) = (4, 11, 8) -- the Type F parents have (5, 12, 9). So moving one
     free-row direction costs one dimension of Omega and one unit of the FO2 bound. (rc45's plane has no equal columns.)
     OPEN and decisive: is there a 6-dim 4x5 level space without a full free row and with FO2 bound >= 9 ? None among ~200.
 4.5 DOUBLE MOVES (reg2/ecmove2.py). Row 3 keeps a 2-dim part U = {w_a = w_b = w_c} or {w_a = w_b, w_c = w_d} of 1^perp and the two
     complementary directions are placed in rows of {0,1,2} (same row, or two rows with orthogonal directions e_a - e_b and
     e_a + e_b - 2 e_c, resp. e_a - e_b and e_c - e_d): 15 of the 20 variants tried are level (6-dim, single-row parts (2,0,0,2),
     (1,1,0,2), ...), all with (dim Omega, dim T_1, FO2) = (3, 10, 8). Empirical law along the chain Type F -> one move -> two
     moves: Omega 5 -> 4 -> 3, T_1 12 -> 11 -> 10, FO2 bound 9 -> 8 -> 8. So in everything found:
          FO2 bound = 9  <=>  full free row (and Omega = C^5);   no full free row  =>  FO2 bound <= 8.
STATUS 19:55: COMPUTE-reg2.md revised (families DR, M*; target (S6-FO2); census E). Final report follows.
 4.6 EXACT certificates (reg2/exact_fo2.py, Fractions; gradient rows at 300 integer points, exact kernel, exact rank of q_Y on it):
       M*_1 with (x,y) = ((1,-1,0),(1,1,-2)), ((2,-1,-1),(0,1,-1)), ((1,2,-3),(5,-4,-1)) and
       M*_2 := e_3 (x) {sum w = 0, w_1 = w_2} (+) {x e_4^T : x in C^3, sum x = 0} (+) C e_2 (e_1 - e_2)^T  (unique up to symmetry):
            dim ker = 11, Omega inside (e_1 - e_2)^perp, rank q = 5  =>  every level space containing the space has dim <= 8  [THEOREM for
            these four spaces, given that they are level (section 4.3 / Lemma EC)];
       Type F parent e_3 (x) 1^perp (+) {x e_4^T}: dim ker = 12, Omega = C^5, rank q = 6: second order allows 9; only FL excludes it.
     Up to row/column permutations the single EC moves of the two known kinds of Type F spaces with Omega = C^5 are exactly M*_2 and the
     one-parameter family M*_1(x). Remark: M* contains rows' split pair e_3 (x) U (+) e_2 (x) U' with U' = C(e_1 - e_2) (two-column m);
     Theorem FL2* gives only dim <= 10 - dim(U o U') = 9 there -- this is the case the team already found delicate (verifyfl's TC5).
STATUS 19:56: final. Scripts added since 19:40: linespan.py, drsearch.py, look3.py, look4.py, mstar2.py, mstar2_fo2.py, exact_fo2.py, ecmove.py,
 ecmove2.py, ext55.py, ext55b.py, ext7.py; data: Mstar2.npy, dr_u3_*.npy, ec_*.npy, ec2_*.npy, linespan_other_*.npy.
 4.7 (reg2/ecmove3.py) EC moves of the Type F row-4 kernels of ex2, ex3, fam2 and the s-family (their N lives on two columns, three
     zero columns): 24 more spaces, all level, all (dim Omega, dim T_1, FO2) = (4, 11, 8). Total: 54 single-move spaces, all (4,11,8).

# ROUND 2 (start 19:59, budget ~2 h). Targets: (1) deletable line at dim 6, (2) (S6-FO2) family by family, (3) a_r = 3, (4) FILTER.
STATUS 20:08: (2) the families with a 3-dim single-row part (M*, EC moves, DR3) are now excluded from 9-dim level spaces by a HAND proof
 (Theorem SP8 below: stage2's (Z3) + verifyfl's TC5 / SPLIT), no computation. (4) FILTER tested. NC family: 10 random members (2,9,7).

## 5. Theorem SP8 and the family-by-family status of "L_r = M, dim L = 9" (round 2)
 5.1 (Z3) in the form used [rigorous; = stage2 (Z3) / rows' saturation; 3 lines]. L level 5x5, i a row, Z_i := {w : e_i w^T in L} (single-row
     part, inside 1^perp), L_i := L cap {row i = 0} (a 4x5 level space), W_i := row-i projection of L. Then
        (a) C(L_i) lies in Z_i^perp cap 1^perp (dim 4 - z_i),      (b) dim L = dim L_i + dim W_i <= dim L_i + 4.
        [FLAG R3 (verify2): "dim W_i <= 4" in (b) is the FK fact a_i >= 1 (W_i never contains 1), not part of the Z3 argument.]
     Proof: for t in L_i, w in Z_i: perm(J + t + e_i w^T) = perm(J + t) + <w, N(J' + pi_i t)>, both permanents are 120.  QED
     So in a 9-dim level space, for EVERY row i (and column), L_i is a 4x5 level space of type (4 + a_i, <= 4 - z_i).
 5.2 THEOREM SP8 [rigorous given verifyfl's TC5, SPLIT and Lemma SL, all verified]. Let L be a level space of 5x5 matrices containing
     e_i (x) U, U = {w : <1,w> = 0, <m,w> = 0} (dim 3), m in 1^perp. If  (a) m = e_a - e_b,  or  (b) <m,m> != 0 and e_i' m^T is in L for
     some row i' != i,  then dim L_i <= 4 and dim L <= 8.
     Proof: by 5.1(a) L_i is level with defect inside C m. (a): TC5 ("a 4x5 space with defect line inside C(e_a - e_b) has dim <= 4").
     (b): e_i' m^T lies in L_i; defect 0: Lemma SL (dim <= 3); defect line C m, non-isotropic, split: Theorem SPLIT (dim <= 4).
     Then 5.1(b).  QED      [Compare rows' FL2*: 10 - dim(U o m) = 7, 8, 9 for |supp m| = 4-5, 3, 2; SP8 gives 8 also for two columns.]
     COROLLARY (regime a_r = 2, hand proof, all parameters): L_r cannot be a member of the families M*_1(x,y), M*_2, any single EC
     move of a Type F space (they contain e_3 (x) {w_a = w_b} and e_i (e_a - e_b)^T), nor a DR3 space containing its split element
     e_i' m^T with <m,m> != 0 (the four DR3 spaces found by drsearch do: m two-column up to 1e-3 in three of them, three-column in one).
     Sanity (pfr_chk.py): in the 7-dim spaces M* (+) C t, row 3 has rank 4, L_3 is a (3,1) space with defect direction e_1 - e_2.
     In general: a 3-dim single-row part e_i (x) {1,m}^perp in a 9-dim level space  <=>  L_i is a (5,1) [or (6,1)] space with line C m:
     [FLAG R3 (verify2): the "<=>" in the previous line is only "=>" (the converse is not proved).]
     the team's open (DI_5) case e = 1, now only for the lines m NOT covered by TC5 / SPLIT / PR3.
 5.3 STATUS TABLE for M = L_r of dimension 6 in a 9-dim level space (census families of section 4):
       F  (full free row)                                    excluded: Theorem FL                          [rigorous]
       M*, EC moves, DR3-split (3-dim single-row part)       excluded: Theorem SP8                         [rigorous]
       DR3 non-split or isotropic m                          none found; would need "no (5,1) with line C m"
       DR2, NC (dim Omega = 2)                               excluded by criterion A: dim L <= 7           [rigorous GIVEN Omega(M) = span(1,e_c);
                                                             Omega computed per space: exact for 2 spaces, numerical for the others]
     So what is missing for a proof of the regime is (i) the classification "6-dim => one of these families" and (ii) a structural
     proof of dim Omega = 2 for DR2 / NC (symbolic tasks G1, G2 in COMPUTE-reg2.md section 7).
 5.4 NC family of section 2.5: 10 random members (fam_nc2.py): (e, dim T_1, dim Omega, FO2, dim E_0) = (3, 9, 2, 7, 7) for all.

## 6. FILTER for regime 1 (rows with 4-dim projection), from criterion A  [statement rigorous; tests numerical, reg2/filter1.py]
 Let L be a 9-dim level space and r a row with a_r = 1 (W_r 4-dim, M := L_r 5-dim). NECESSARY:
   (F1) M is a 4x5 level space with Phi = 0 on M (all five 4x4 subpermanents vanish identically)           [stage2 (Q-r)(ii)]
   (F2) Omega(M) = C^5, i.e. dim T_1(M) = dim E_0(M) + 5: EVERY e_j (j = 0..4) is the row-r part of a first-order extension, equivalently
        each deletion permanent N_j(J'+Y) restricted to M is of the form -D_X F(J'+Y) (g(M) = e(M) + 1: all defect functions twisted-
        realisable). Proof: W_r (dim 4) lies in Omega(M) and misses 1, which is in Omega(M).   [new, cheap: one SVD]
   (F3) for every OTHER row i: L_i is a (4 + a_i, <= 4 - z_i) space (5.1); in particular a 3-dim single-row part of M in row i forces a
        (5,1) space with that line, impossible in the cases of SP8.
   (F4) FO2 bound(M) >= 9.
 Tests (5-dim spaces; invariants (Phi-rank, dim Omega, dim T_1, FO2)):
   generic hyperplane of a Type F space with Omega = C^5 (F1 = free row (+) {x e_4^T}, F2 = free row (+) C x e_0^T (+) C y e_3^T):
        (0, 5, 12, 9), single-row part of dim 3 with a GENERIC line m: passes F1, F2, F4. By (F3) it is a regime-1 candidate exactly if a
        (5,1) space with a generic line exists: these hyperplanes are the "(5,1) problem" seen from the other side.
   hyperplane of F1/F2 obtained by dropping a free-row direction: (0, 5, 13, 9): same remark (m two-column: excluded by SP8(a)).
   generic hyperplane of M*_1, M*_2: (0, 4, 11, 8): FAILS (F2) and (F4).
   special hyperplanes of M*: drop x e_0^T or y e_3^T: (0, 4 or 5, 15, 10): pass first/second order, but contain the split pair: excluded
        by SP8(b) -- an example where SP8 is strictly stronger than FO2; drop the EC element: (0, 5, 15, 10), m two-column: SP8(a).
   5-dim census of round 1 (ext5.py, 53 spaces): Omega = C^5 with Phi = 0 in 10 of them: 9 with a full free row, 1 without.
 So (F2) removes most 5-dim level spaces, and what survives so far all contains a 3-dim piece of a free row, i.e. reduces by (F3) to (5,1).

## 7. Deletable lines, maximality and the 7-dim question (targets 1 and 3)   [rigorous unless marked]
 7.1 LEMMA DL. For a 4x5 level space M:  (a) row i is deletable (pi_i(M) is a 3x5 level space)  <=>  d_i := (e_i - (1/4) 1) (x) 1 lies in E_0(M);
     (b) column c neutral (N_c(J'+Y) = 24 on M)  =>  d^c := 1 (x) (e_c - (1/5) 1) lies in E_0(M);
     (c) P_2(d_i + Y) = -15/2 and P_2(d^c + Y) = -24/5 for every Y in M.
     Proof. (a) D_{e_i 1^T} F(J'+Y) = 2 F_3(rows != i of J'+Y) (each injection of three rows into five columns misses two columns) and
     D_{J'} F(J'+Y) = 480 (L1(c)); so D_{d_i} F = 2 F_3 - 120 vanishes iff F_3 = 60. (b) Let p = perm_4, A = J_4 + Y^(c), v = 1 + y_c.
     Level and neutral: F = p(A) + D_{v 1^T} p(A) = 120, p(A) = 24, so D_{v 1^T} p(A) = 96; M^(c) is a linear level space, so
     D_{Y^(c)} p(A) = 0 and D_{J_4} p(A) = 4 p(A) = 96; hence D_{1 e_c^T} F(J'+Y) = D_{J_4} p(A) = 96 = D_{J'}F / 5.
     (c) b'(d, Y) = D_d P_2(Y) = 0 for d in E_0(M), and P_2(x (x) 1) = -10 sum x_i^2, P_2(1 (x) y) = -6 sum y_j^2 for sum-zero x, y.  QED
 7.2 PROPOSITION MAX. If M has a deletable row or a neutral column and dim E_0(M) = dim M + 1, then M is a maximal 4x5 level space.
     (Any level space containing M lies in E_0(M) = M + C d, and P_2(d + Y) != 0.)  All 41 spaces of sections 2.1-2.2 and the
     exact members of sections 2.5, 4.3 satisfy the hypotheses numerically (dim E_0 = 7).
 7.3 COROLLARY (what a 7-dim 4x5 level space M_7 must look like). (i) no full free row (rows' SL_3 corollary); (ii) no two equal
     columns (upstream L_gct_215, abbrev eI, Lean-checked); (iii) every 6-dim subspace M_6 has E_0(M_6) containing M_7; if M_6 has a
     deletable row or neutral column then dim E_0(M_6) >= 8 (the direction d is in E_0(M_6) but not in M_7). In particular a 7-dim space
     with a neutral column c (or deletable row) has ALL its 6-dim subspaces of this kind -- never seen: every 6-dim level space found
     (about 250 by now) has a deletable line and dim E_0 = 7 [numerical].
     So: "every 6-dim 4x5 level space has a deletable row or neutral column and dim E_0 = 7"  ==>  no 7-dim 4x5 level space  ==>  a_r <= 2.
     (iv) [numerical] extension search for dimension 7 through 45 known 3-,4-,5-dim spaces: 0 of 132 starts (ext7.py; N = 330 sample
     points = number of monomials, see COMPUTE-ERRATA A5: to be redone with N >= 400 on the 24-core machine).
     For a 9-dim L with a_r = 3: M_7 = L_r must in addition have dim Omega(M_7) >= 3 (criterion A) and e(M_7) <= 4 - z_r (5.1).
 7.4 What upstream L_gct_215 contains (read: statements only; proofs are 7.5k obfuscated lines). Case tree for an 8-dim L by u_i = dim of the
     single-row part of row i and p_ij = rank of the projection to rows i, j:  u_i >= 4 (aG7: then dim <= 7);  2 <= u_i <= 3 (MidCase);
     u_i = 1 (mI: produces a 7-dim level space with two equal columns; eI: none exists; the 7-dim lemmas vR, uQ, aAp, aGk, xQ, aEu, vU,
     aEv, aDh are all UNDER the equal-columns hypothesis);  all u_i = 0 (HighPair: some p_ij = 7; vK: all p_ij <= 6).
     General tool (aBu, pure linear algebra, any dimension d):  d + r_i <= p_ij + p_ik + u_l  for distinct rows i, j, k, l.
     Nothing in the file classifies 6- or 7-dim spaces; at dim 6 the tree gives only the case distinction itself. With 5.1 the cases read,
     for M = L_r (dim 6) inside a 9-dim L and a row i != r:  u_i = 4: FL;  u_i = 3: L_i is a (5 or 6, 1) space with line C m (SP8 closes
     m two-column and the split non-isotropic case);  u_i = 2: L_i is a (5,2) space [or (6,2)], a_i = 1;  u_i <= 1 for all i: the
     neutral-column / single-column side (transposed 5.1 for the column c).  Target (1) is NOT proved.
 7.5 EMPIRICAL LAW (EL) [numerical, reg2/autest.py: 55 rows of 29 six-dim spaces, 0 violations, equality in 47]:
        for a 6-dim 4x5 level space M and every row i with single-row part e_i (x) U_i:   Omega(M) lies in A(U_i) := {s : U_i o s in U_i + C1}.
     It is NOT a formal consequence of "e_i w^T in M": for (X;rho) in T_1(M), w in U_i, Y in M one has the exact identity
        perm[pi_i(J+Y) ; w o rho] = sum_k perm[pi_i(J+Y) with row k replaced by X_k - rho - Y_k o rho ; w]      (rows k != i, r)
     (column scaling of perm[Z ; w], which vanishes on pi_i(CJ + M) by 5.1), and the right side need not be a multiple of F: (EL) fails
     for one 3-dim subspace of a line-spanned space (lemA_test.py; deviation 5e-2), while it holds to 1e-14 on all 6-dim spaces.
     CONSEQUENCE IF (EL) HOLDS for L_r in regime a_r = 2 (Omega contains k^perp, dim 4): every single-row part U_i (i != r) of L is
     0, C k, k^perp cap 1^perp or 1^perp, and k = e_a - e_b is a two-column vector as soon as some U_i != 0, 1^perp [A(Cw) has dim
     6 - |supp w| or <= 2]. The last two cases are excluded (SP8(a), FL), so all single-row elements of L outside row r would be
     multiples of e_i (e_a - e_b)^T with u_ra = u_rb on L^.  (Stated as a target; not proved.)
STATUS 20:25: msolve / Singular runs (reg2/gb/): the NC family of 2.5 and the whole support pattern (2,2|2) are now settled EXACTLY
 (char 0, all charts, calibrations non-unit). verify2's remark checked: (S6-FO2) + FL exclude a_r = 3 as well (section 8.1).

## 8. Exact results with msolve / Singular (round 2; scripts reg2/gb/polylib.py, famtool.py, gen_nc.py, gen_dr22.py; reg2/dr22_exact.py)
 8.1 Two remarks [rigorous].
   (a) q_0 := D^2 perm(J) = 12 P_2 and tau_r = J - 5 e_r 1^T lies in T_1(M) for every M, with P_2(tau_r) = -200. So the rank of q_0 on T_1(M) is
       >= 1 and  FO2 bound(M) <= dim T_1(M) - 1  ALWAYS: every level space containing M has dim <= dim T_1(M) - 1. In particular
       dim T_1(M) <= 9  ==>  (S6-FO2) for M; and (S6-FO2) for M with dim T_1 = 10, 11 means rank q >= 3, 5.
   (b) (S6-FO2) + FL  ==>  no 9-dim level space has a row or column with a_r >= 2 -- INCLUDING a_r = 3: if dim L_r >= 6 take any 6-dim
       subspace M_6 of L_r; either M_6 contains a full free row (then L does: dim L <= 7 by FL) or FO2 bound(M_6) <= 8 and L contains M_6.
       (My round-1 statement "a_r = 3 needs the non-existence of 7-dim 4x5 spaces" was unnecessarily weak: the FO2 bound holds for every
       level space CONTAINING M_6, not only for those with L_r = M_6.)
 8.2 THEOREM NC-FAM [EXACT, char 0]. For every member M(w0,w1,w3) of the family of section 2.5 (w_i != 0):
        Omega(M) = span(1, e_0),   E_0(M) = M (+) C d^0 (d^0 = 1 (x) (5 e_0 - 1)),   dim T_1(M) = 9.
     Hence: L_r = M => dim L <= 7 (criterion A); every level space containing M has dim <= 8 (8.1(a)); M is a maximal 4x5 level space (7.2).
     Method (gen_nc.py): variables w0, w1, w3 (12), X (20), rho (5); equations: the 7 family relations, the 32 coefficient equations of
     D_t perm(J + (Y;0)) = 0 in y (the polynomial has only 32 monomials in y), a parameter chart a_1 = 1, b_j = 1, c_l = 1 (five charts
     (1,1,1), (1,1,2), (1,2,1), (1,2,2), (1,2,3) cover all members up to the S_4 symmetry of the columns 1..4), and
       Omega-test: rho_0 = 0, rho_1+..+rho_4 = 0 (allowed: subtract tau and e_r (5e_0 - 1)^T), chart rho_j = 1 (j = 1..4): 20 systems;
       E_0-test:   rho = 0, column 0 of X zero, x_{0,ja} = x_{1,jb} = x_{3,jc} = 0 (X modulo M + C d^0), chart x_ib = 1: 65 systems.
     Results: UNIT IDEAL in all 85 systems over Q (Singular std, 14 s + 3 s) and modulo 65521, 2147483629, 1073741789 (msolve, 4 s each).
     Calibrations (must be non-unit, and are, over Q and mod p): rho = e_0 (basis sizes 151-187); column 0 of X free with x_00 = 1 (110-123).
 8.3 THEOREM DR22 [EXACT, char 0]: the complete support pattern (2,2|2) (two rows with 2-dim single-row parts, one column with a 2-dim
     single-column part, direct sum of dimension 6).
     (i) [hand] P_1, P_2 force, up to the symmetries: U_0 = {w : w_0 = 0, sum w = 0, <mu,w> = 0} (mu in C^4 on columns 1..4, not
         constant), U_1 = (U_0 + C1)^perp cap 1^perp = span(5 e_0 - 1, mu~ - mean), V = {x : x_1 = 0, sum x = 0};
         M(mu) := e_0 (x) U_0 (+) e_1 (x) U_1 (+) V (x) e_0.   [cases: both row parts vanishing at column 0, or V vanishing at both rows,
         are impossible by dimension.]
     (ii) [exact] in the chart mu = (0,1,m3,m4) ALL coefficients of F(J'+Y) - 120 vanish identically: M(mu) is level for EVERY mu.
          Row 1 is deletable, e = 4, no neutral column, no full free row.
     (iii) [exact] E_0(M(mu)) = M (+) C d_1 for every (m3,m4) (13 X-charts, elimination ideal (1)).
     (iv) [exact] in each of the four rho-charts the elimination ideal of {(m3,m4) : Omega not inside span(1,e_0)} is (m3^2 - m3, m4^2 - m4)
          (over Q and mod two 31-bit primes). So for mu NOT a 0/1 vector: Omega = span(1, e_0), dim T_1 = 9: dim L <= 7 if L_r = M, and <= 8
          for every level space containing M.
     (v) [exact, Fractions] the four special members mu = (0,1,0,0), (0,1,0,1), (0,1,1,0), (0,1,1,1) (mu = indicator of a column set T;
          two orbits): dim T_1 = 10, Omega = span(e_0, 1_T, 1_{T^c}) (dim 3), rank q = 4: every level space containing them has dim <= 8.
     So (S6-FO2) holds on the whole pattern (2,2|2). Calibration: rho = e_0 is non-unit (basis size 21). Numerics agree (dr22_num.py).
 8.4 Pattern remarks [hand]. In a line-spanned space the P_2 conditions are: <u,u'> = 0 for single-row elements in different rows, and
     u_c x_i = 0 for e_i u^T and x e_c^T. Hence for a row with a 3-dim part U = {1,m}^perp every single-row element in another row is a
     multiple of e_i' m^T: the patterns (3,1|2), (3,1|1,1) always contain the split pair, and SP8(b) applies when <m,m> != 0.
     Not yet treated exactly: (2,1,1|2) and the NC patterns (3|3), (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1), (1,1,1|2,1)
     (all (2,9,7) numerically); precise task in COMPUTE-reg2.md section 7.

STATUS 20:35 (END OF ROUND 2, stopped on the coordinator's instruction): handover written: handover/HANDOVER-reg2.md.
 Added after section 8 was written: pattern (2,1,1|2) case (iii) EXACT (level for every mu; Omega = span(1,e_0), E_0 = M + C d_1 for every
 mu; reg2/gb/gen_dr211.py); case (ii) (reg2/gb/gen_dr211b.py): level conditions = P_2 relations + triple product, calibration non-unit,
 but the Omega-test over Q is NON-UNIT in chart (1,2,3), rho_2, rho_3, rho_4: UNDECIDED whether these members have a larger Omega
 generically; their (dim T_1, dim Omega, FO2) were NOT computed (reg2/dr211b_num.py is written but not run). First pending task.
 Small lemma not recorded above (P8 of the handover): a level 4x5 space with an identically zero column has that column neutral.
 [merged at 20:36 UTC from the cloud copy; reg2 round 3: the "dr211b_num.py" named here did not exist on this machine and was re-written]
# ROUND 3 (reg2, start 19:45 UTC on the 24-core machine; times below are UTC). Targets: REG2-T1 (2,1,1|2) case (ii); families toward
# (S6-FO2); census E.  (No handover file existed; the round-2 work after section 8.4 survives only as reg2/gb/gen_dr211{,b}.py.)
STATUS 20:00: case (ii) re-parametrised by hand (a, b, c pairwise orthogonal in H, T(a,b,c) = 0; a = cross4(b,c)); numerically generic
 members (dim E_0, dim Omega, dim T_1, FO2) = (7, 2, 9, 7); mod-p eliminations (msolve, all charts) give the special locus of Omega:
 b, c sharing a zero column (curves) and b, c with disjoint two-column supports (one orbit), where (dim T_1, rank, FO2) = (10, 4, 8)
 numerically; E_0-test unit in all 156 charts mod 65521. Singular over Q running (reg2/gb/runs/dr211q.log).

## 9. REG2-T1: the support pattern (2,1,1|2) (round 3)
 Setting (TASK X1): M = e_{i0} (x) U_0 (dim 2) (+) C e_{i1} u_1^T (+) C e_{i2} u_2^T (+) V (x) e_0 (dim 2), direct sum of dim 6. H := sum-zero
 vectors of C^4 on the columns 1..4 (3-dim, the bilinear form is nondegenerate on H), w = (w_0, w') for w in C^5, T(a,b,c) := sum_j a_j b_j c_j,
 e(u,b,c) := sum over distinct j,k,l of u_j b_k c_l = (Su)(Sb)(Sc) - (Su)<b,c> - (Sb)<u,c> - (Sc)<u,b> + 2 T(u,b,c)  (S = coordinate sum).
 P_2 <=> the row parts are pairwise orthogonal and for each row i in {i0,i1,i2}: U_i vanishes at column 0 or V vanishes at row i (8.4).
 A 2-dim V inside 1^perp of C^4 vanishes at <= 1 row, so there are three incidence cases: (i) V vanishes at none of i0, i1, i2;
 (ii) V vanishes at i0; (iii) V vanishes at i1 (or i2).  Rows i0, i1, i2 = 0, 1, 2 below unless said otherwise.
 9.1 CASE (i) IS EMPTY [rigorous, hand]. All row parts lie in (0,H). U_0' (2-dim) is orthogonal to b, c (U_1 = C(0,b), U_2 = C(0,c)), so b, c lie in
     the line U_0'^perp cap H; <b,c> = 0 forces c ~ b isotropic and U_0' = b^perp cap H, which contains b: U_0 = span((0,a'),(0,b)). The only
     surviving P_3 terms come from rows {0,1,2} without column 0: P_3 = y3 y4 e(u', b, b) = 2 y3 y4 (y1 <a', b o b> + y2 sum b_j^3) (all other
     triples carry a factor <u,b>, <b,b> or a coordinate sum). So sum b = sum b^2 = sum b^3 = 0, hence (Newton) b ~ chi_1 = (1, i, -1, -i) up to
     order; with chi_k = (i^{kj})_j one has <chi_k, chi_l> = 4 delta_{k+l = 0 mod 4}, b^perp cap H = span(chi_1, chi_2), and <a', chi_2> = 0 forces
     a' in C b: dim U_0 = 1, contradiction.  QED
 9.2 CASE (iii) [rigorous, hand]: U_0 = (0, U_0'), u_2 = (0,c), c spans U_0'^perp cap H, u_1 = alpha (5 e_0 - 1) + (0,h) with h in H orthogonal to
     U_0' + Cc. If U_0' is nondegenerate, U_0' + Cc = H and h = 0. If U_0' = r^perp cap H (r isotropic, c ~ r) then h = beta r and the P_3 terms are
     all zero except rows {0,1,2} without column 0: P_3 = 2 beta y3 y4 <u', r o r>, P_4 = x3 * (same); r o r is never in span(1, r) for isotropic
     r != 0 in H (r o r = lam 1 + mu r gives lam = 0 from the coordinate sum, then r_j in {0, mu} and sum r = 0 gives r = 0), so beta = 0.
     Hence case (iii) is exactly round 2's family (reg2/gb/gen_dr211.py): U_0' = c^perp cap H, u_1 = 5 e_0 - 1, u_2 = (0,c), c in H \ 0 arbitrary
     (chart mu = (0,1,m3,m4), c = mu - mean), and it is LEVEL FOR EVERY c ['lev' mode: the level ideal is (0), exact]. Row 1 is deletable.
     Numerically (reg2/dr211iii_num.py, 10 members incl. 0/1 vectors): (dim E_0, dim Omega, dim T_1, FO2) = (7, 2, 9, 7) always. Exact: 9.6.
 9.3 CASE (ii) [rigorous, hand]: U_1 = C(0,b), U_2 = C(0,c), V = {x : x_0 = 0, sum x = 0} (forced), U_0 inside S := {w : sum w = 0, w' perp b, c}.
     (g) b, c independent: S is 2-dim, U_0 = S = span(5e_0 - 1, (0,a)) with a := cross4(b,c) (signed 3x3 minors of [1;b;c], orthogonal to 1, b, c).
     (d) c ~ b (then b isotropic): S is 3-dim; P_3 = 2 y3 y4 <u', b o b> (same bookkeeping as 9.1) forces U_0 = S cap (0, b o b)^perp =
         span(5e_0 - 1, (0,a)) with a = cross4(b, b o b)  [b o b is not in span(1,b), 9.2].
     In both: P_2 = -(y2y3<a,b> + y2y4<a,c> + y3y4<b,c>) and P_3 = 2 y2 y3 y4 T(a,b,c), P_4 = 2 x3 y2 y3 y4 T(a,b,c). So
          CASE (ii) = { ([a],[b],[c]) : a, b, c in H \ 0 pairwise orthogonal, T(a,b,c) = 0 }   (a 2-dim variety; M depends on the three lines).
     Row 0 is deletable (V vanishes at row 0; M_0 level gives F_3 = 60), so d_0 = (e_0 - 1/4) (x) 1 lies in E_0 (Lemma DL).
 9.4 THEOREM DR211-ii [EXACT, char 0; numerics agree].  For EVERY member M of case (ii):
     (a) E_0(M) = M (+) C d_0, dim E_0 = 7;
     (b) dim Omega(M) = 2 (Omega = span(1, e_0)), hence dim T_1 = 9, UNLESS a is two-valued, i.e. M lies in
           SIGMA_k (k = 1..4): b, c in H_k := {w in H : w_k = 0} (then a ~ 1 - 4 e_k, c ~ b x 1 inside H_k; a curve P^1 of members), or
           D: {b, c} = {e_i - e_j, e_k - e_l} with {i,j,k,l} = {1,2,3,4}, a = e_i + e_j - e_k - e_l (one orbit);
         [a two-valued <=> (b,c) in SIGMA or D: if a ~ 1 - 4e_k then b, c are in H cap a^perp = H_k; if a ~ (1,1,-1,-1) then b, c lie in
          span(e_1-e_2, e_3-e_4), and <b,c> = 0 = T(a,b,c) give x x' = y y' = 0.]
     (c) on SIGMA and D: dim T_1 = 10 and rank q >= 3, so the FO2 bound is 8 (exact rank 4 at every rational member tested).
     CONSEQUENCE: (S6-FO2) holds on the whole case (ii): FO2 bound <= 8 for every member (dim T_1 = 9 gives <= 8 by 8.1(a); numerically 7),
     = 8 on SIGMA and D. Together with 9.1 and 9.6 below: (S6-FO2) on the whole pattern (2,1,1|2).
     Remark: the special locus is exactly where A(U_0) = {s : U_0 o s in U_0 + C1} has dim 3 (U_0 + C1 = {w : w' in span(1', a)}, and
     A(U_0) = span(1, e_0) unless a o a lies in span(1,a), i.e. a two-valued): consistent with the empirical law (EL) of 7.5 for the deletable row.
     PROOF / METHOD.  Parametrisation (reg2/gb/gen_dr211d.py + dr211_common.py): b = (b1,b2,b3,-b1-b2-b3), c likewise, a = cross4(b,c) (g)
       resp. c = b, a = cross4(b, b o b) with <b,b> = 0 (d); charts b_1 = 1 (S_4 symmetry of the columns 1..4), c_1 = 1 or c_2 = 1 (residual S_3),
       a_ja != 0 via z*a_ja - 1 (ja = 1..4) -- these charts cover every member.  FO equations = coefficients in y of
       sum_{ij} t_ij cof_ij(J + (Y;0)) (famtool.py); the level equations of the family are added (they are <b,c> and T).
       Normalisation of X modulo M + C d_0: x00 = x10 = x20 = x34 = x_{0,ja} = x_{1,jb} = x_{2,jc} = 0 (pivot determinant ~ a_ja b_jb c_jc != 0).
       Omega-test: rho_0 = 0, rho_1+..+rho_4 = 0, rho_jr = 1 (jr = 1..4), eliminate z, X, rho:   48 systems (32 for (g), 16 for (d)).
       E_0-test: rho = 0, X normalised, x_ib = 1 for each of the 13 free coordinates: 156 systems.
       Singular std / eliminate over Q (logs reg2/gb/runs/dr211q.log, dr211q_ge0.log; outputs /tmp/dr211q/*.qout), cross-checked mod 65521 with
       msolve -e (/tmp/dr211d): E_0-tests: UNIT in all 156 (Q and mod p). Omega-tests: the elimination ideals have minimal primes exactly the
       components of SIGMA (b, c sharing a zero column) and the D points, identical over Q and mod p in every chart (reg2/gb/minass_q.py).
       Calibrations NON-unit (Q and mod p): rho = e_0 (12 systems; elimination ideal = the family ideal) and x34 = 1 with the d_0 pivot released
       (Q: 7 of 12 run, all non-unit, basis sizes 41-53; mod p: 12 of 12).
     (c) by exact computation (reg2/dr211_special.py, sympy over Q / Q(s); the FO matrix is the FULL coefficient matrix, so its kernel IS T_1):
       SIGMA_4 chart b = (1, s, -1-s, 0), c = (1+2s, -2-s, 1-s, 0), a = (1,1,1,-3): symbolic level identity; generic rank 15 (dim T_1 = 10);
       Omega-test on the curve with the 3-dim normalisation rho_0 = rho_4 = 0 = rho_1+rho_2+rho_3 (complement of span(1, e_0, 1_{123})): elimination
       ideal (1) for both pivot charts (reg2/gb/gen_s4.py; calibration rho = 1_{123}: ideal (0)), so dim Omega <= 3 and dim T_1 <= 10 on all of SIGMA_4;
       q_Y on a polynomial basis N(s) of ker A(s): gcd over all principal 3x3 minors (three choices of Y) = (s-1)^4 (s+1)^4, so rank q >= 3 for
       s != +-1; at s = 1, s = -1 and at the remaining point b = (0,1,-1,0): exact rational certificate dim T_1 = 10, rank 4, bound 8.
       (The isotropic points s = omega, omega^2 of SIGMA_4 are the members of component (d) on SIGMA: covered by the same symbolic computation.)
       D: exact certificate (b,c) = (e_1-e_2, e_3-e_4): dim T_1 = 10, rank 4, bound 8.  SIGMA_k, k != 4, and the other D points: column symmetry.
 9.5 COROLLARY [hand]: in case (ii) every member has a deletable row (row 0) and e = 4; it has no neutral column and no full free row.
 9.6 THEOREM DR211-iii [EXACT, char 0].  For EVERY member of case (iii): dim Omega <= 2 and dim E_0 <= 7, so dim T_1 <= 9 and the FO2 bound is <= 8.
     (Round-2 generator reg2/gb/gen_dr211.py, run this round over Q, log reg2/gb/runs/dr211iii.log: 'elim' -- Omega-test rho_1+..+rho_4 = 0,
     rho_jr = 1 with X free: elimination ideal (1) in all four rho-charts [hyperplane argument: then Omega cap {sum_{j>=1} rho_j = 0} lies in C e_0,
     so dim Omega <= 2]; 'e0' -- X normalised modulo M + C d_1 with two pivot sets N1 (x21, valid for S := 1+m3+m4 != 0) and N2 (x22, valid for
     S != 4): elimination ideal (1) in 10 of 13 charts and (S) resp. (S - 4) in the other 3, i.e. unit wherever the normalisation is valid; the
     chart mu = (0,1,m3,m4) covers every member up to the S_4 symmetry of the columns 1..4. Calibration rho = e_0: non-unit.)
     Hence THE WHOLE PATTERN (2,1,1|2) SATISFIES (S6-FO2): case (i) empty (9.1), case (ii) bound <= 8 (9.4), case (iii) bound <= 8 (9.6).  REG2-T1 DONE.
 9.7 Pattern (3,1|2) [hand + exact]. U_0 = {1,m}^perp in row 0, the row-1 part is C m (8.4), V 2-dim in column c. Incidences: (beta) V vanishes at
     row 1 and U_0 at column c: m ~ 5 e_c - 1, non-isotropic: SP8(b).  (gamma) impossible.  (alpha) V = {x_0 = 0, sum x = 0} and m_c = 0 (c = 4):
     M(m) = e_0 (x) {1,m}^perp (+) C e_1 m^T (+) {x e_4^T : x_0 = 0, sum x = 0}; ALL P_3, P_4 terms vanish (rows 2, 3 both need column 4, and
     the remaining triples carry <u,m> or a coordinate sum): LEVEL FOR EVERY m with m_4 = 0 [hand; exact: no level equations].
     EXACT (reg2/gb/gen_p312.py over Q; chart m_0 = 1 by the S_4 symmetry of the columns 0..3; constant pivots, no localisation; log runs/p312.log):
       E_0-test unit in all 13 charts (calibration non-unit): dim E_0 = 7 for every m;  Omega-test (complement of span(1, e_4)): elimination ideal
       (m1 m2 (m1+m2+1)), i.e. dim Omega = 2 and dim T_1 = 9 unless m has a zero among the columns 0..3 (|supp m| <= 3). Calibration e_4: non-unit.
     Special members |supp m| <= 3: two-column m: SP8(a) (numerically (11,5,8) = M*_2); three-column non-isotropic: SP8(b) (numerically (10,4,8));
     three-column ISOTROPIC m = (1, w, w^2, 0, 0) (one orbit): EXACT over Q(sqrt -3) (reg2/p312_special.py): level identity, dim T_1 = 10,
     rank q = 4, FO2 bound 8.   So pattern (3,1|2): every level space containing a member has dim <= 8 -- in particular for ISOTROPIC m,
     where SP8 says nothing. [(S6-FO2) itself is proved for all members except the 3-column non-isotropic curve, where SP8 gives the same
     consequence; numerically FO2 = 8 there.]
STATUS 20:24: REG2-T1 DONE: pattern (2,1,1|2) satisfies (S6-FO2) [case (i) empty by hand; (ii) exact over Q incl. special locus SIGMA u D with FO2 = 8; (iii) exact over Q, dim T_1 = 9]. Pattern (3,1|2) closed for isotropic m (exact, Q(sqrt-3)); (3,1|1,1) isotropic m: dim T_1 <= 10 exact, rank/special point running.
 9.8 Pattern (3,1|1,1) [hand + exact]. Row 0: U_0 = {1,m}^perp, row 1: C m, columns c, c': C x, C x' (<x,x'> = 0). m non-isotropic: SP8(b) (the
     split element e_1 m^T is in M); m = e_a - e_b: SP8(a). For ISOTROPIC m: m ~ 5e_c - 1 is impossible, so x_0 = x'_0 = 0, and the row-1 incidences
     leave (A) m_c = m_c' = 0 (then m ~ (1, w, w^2) on the three other columns), (B) m_c = 0, x'_1 = 0 (x' ~ (0,0,1,-1), x ~ (0,2,-1,-1)), (B') = (B)
     with c, c' swapped; (C) x_1 = x'_1 = 0 contradicts <x,x'> = 0. Both (A) (x in {x_0 = 0, sum = 0} free, x' = x cross 1 on rows 1..3) and (B)
     (m on the isotropic conic, m_4 = 0, c' = 0 by symmetry) are LEVEL for all parameters [exact: no level equations].
     EXACT (reg2/gb/gen_p311.py over Q, w^2+w+1 = 0 as an equation, pivots localised by z; log runs/p311.log, p311_A0.log):
       (B): E_0-test unit (13 charts, both m-charts); Omega-test (complement of span(1,e_4)): special locus = m three-column (m = (1,w,w^2,0,0) up
            to the columns 1..3, one orbit): dim T_1 = 9 elsewhere; the special member: EXACT over Q(sqrt -3) (reg2/p311_rank.py Bpt): (10, rank 4, 8).
       (A): E_0-test unit, Omega-test with the 3-dim normalisation (complement of span(e_3, e_4, 1_{012})) unit in both x-charts and both pivot
            charts: dim T_1 <= 10 for every member (calibration rho = e_3 non-unit). rank q: EXACT = 4 (bound 8) at x = (0,0,1,-1) and at p = 0, 1, 2,
            -3, 1/3 (reg2/p311A_pts.py, Q(sqrt -3)); numerically (10,4,8) at random complex p.  NOT YET PROVED: rank q >= 3 for EVERY p (a symbolic
            computation over Q(w)(p) is needed: note M is in the radical of q on T_1, so span(M, d_0, tau) has rank <= 2 and the lifts of
            rho = e_3, e_4 must be computed; reg2/p311_rank.py A1 tried span(M,d_0,tau) and got 0 nonzero 3x3 minors, as it must).
     So for the gap: pattern (3,1|1,1) is closed EXCEPT the one-parameter family (A) off the sampled points [exact at 6 points, numerical].
     [SUPERSEDED at 20:38 by 9.11: the whole family (A) is now closed exactly.]
 9.9 Pattern (3|3) [hand + exact]: V_c = all of {sum x = 0} cannot vanish at row 0, so U = {w : w_c = 0, sum w = 0}; the single space
     M = e_0 (x) {w_4 = 0, sum w = 0} (+) {x e_4^T : sum x = 0} is level (no P_3/P_4 terms) and EXACTLY (dim T_1, dim Omega, rank q, bound) = (9, 2, 3, 7)
     (reg2/p33_cert.py).
 9.10 Line-spanned status after round 3 (TASK X1): DONE (S6-FO2 or SP8, exact): (1,1,1|3) [R2], (2,2|2) [R2], (2,1,1|2), (3,1|2), (3|3);
     (3,1|1,1) [family (A) closed by 9.11]. NOT DONE: (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1), (1,1,1|2,1), and the
     "no 6-dim member" claim for the remaining patterns.  Recurring structure seen in every pattern so far (EL-type): generic dim T_1 = 9 with
     Omega = span(1, e_c) (c = a column carrying a single-column part) and E_0 = M + C d_i (i = the deletable row); the jump locus is exactly where
     the deletable row's part U makes A(U) = {s : U o s in U + C1} larger (two-valued annihilator vectors), and there dim T_1 = 10, rank q = 4.
STATUS 20:29: sections 9.1-9.10 written, RESULT ROUND 3 on top, COMPUTE-reg2 section 8 added; (3,1|1,1)(A) rank on the whole curve left open (exact at 6 points).
 9.11 TASK X5 DONE [EXACT, char 0] (reg2/gb/p311A_rank.py, log runs/p311A_rank.log): for EVERY member of (3,1|1,1) case (A) the FO2 bound is <= 8.
     Method: M lies in the radical of q_Y on T_1 (q_Y(t, Y') = D_{Y'} D_t perm(J+Y) = 0 for t in T_1, Y' in M), so the lifts are needed. Unknown lifts
     t_3 = (X3; e_3), t_4 = (X4; e_4) with X normalised by the pivots of gen_p311.py (x01,x02,x03,x10,x13|x23,x14|x24,x20; localisation z); Singular
     over Q in the ring (a.., b.., w, p, z) with block order: the elimination ideal of {FO equations of both lifts, pivots, localisation, w^2+w+1} is
     exactly (localisation, w^2+w+1) [lifts exist for every member] and every a_ij, b_ij reduces to a polynomial in (w,p,z) [lifts unique]; the Gram
     matrices of q_Y (Y = (1,2,-1,3,1,-2), (2,-1,1,1,-3,1)) on span(4 d_0, tau, t_3, t_4) reduced modulo the basis; their 3x3 minors plus the
     elimination ideal generate (1) -- in both pivot charts of x = (0,1,p,-1-p) and in the chart x = (0,0,1,-1). Hence rank q >= 3, and with
     dim T_1 <= 10 (9.8) the bound is <= 8.  (Sample certificates: rank 4 at 6 members.)
STATUS 20:39: (3,1|1,1) closed (9.11). Merged the 6 cloud lines (end of round 2) and flagged verify2's two SP8 wording slips in place. Writing final report.

# ROUND 4 (reg2, start 20:45 UTC). Targets: (1) prove EL for a deletable row; (2) TASK X1' (six NC patterns); (3) census E -> QUEUE.
STATUS 20:41: round 4 started. First remark on (1): EL is FALSE for small deletable-row spaces (M = C e_0 u^T, u = e_1 - e_2: Omega = C^5 but
 A(Cu) = {s_1 = s_2}), so any proof must use saturation U = (C(M_0) + C1)^perp (rows' defect construction) or dimension; testing EL-SAT numerically.

## 10. Round 4, target 1: the law EL for a deletable row
 Setting: M = S (+) e_i (x) U (row i deletable: the row-i projection of M is its single-row part U; S = M cap {row i = 0}).
 A(U) := {s : U o s in U + C1};  EL claims Omega(M) inside A(U).  Equivalent forms [rigorous, hand]:
   (a) s in A(U)  <=>  s o v in U^perp for every v in U^perp cap 1^perp.
   (b) With rows 0 (= i) and 4 of the 5x5 picture, perm(J + Y + eps t) = a^T Gamma(K) b, a = row 0, b = row 4, K = the three middle rows,
       Gamma_{jk}(K) = perm_3(K without columns j,k) (symmetric, zero diagonal). Level <=> G(K) := Gamma(K) 1 lies in U^perp and 1^T G = 120 on
       K in J'_3 + S'.  For t = (X_0; X'; rho): t in T_1  <=>  (C0) <rho + X_0, G(K)> + D_{X'} (1^T G)(K) = 0  and
       (H) Gamma(K) rho + (D_{X'} Gamma(K)) 1 in U^perp, for all K in J'_3 + S'.  Column scaling (D_{K D_s} Gamma = (sum s) Gamma - D_s Gamma - Gamma D_s)
       turns (H) into  <u o rho, G(K)> = D_{X' - K D_rho} <u, G(K)>  for all u in U  (*).
   (c) Hence, if U is SATURATED (U = (C(S) + C1)^perp, rows' defect construction), EL <=> the right side of (*) is constant (= 24 <u,rho>) on
       J'_3 + S'; splitting (*) by degree in Z (K = J'_3 + Z, G = sum_k g_k(Z), g_k(Z)_j = (4-k)! P_k(Z without column j)):
       (H_k)  pi( (4-k)! [ sum_{|T| = k, j not in T} rho(T + j) P_T(Z) ]_j ) = pi( D_{X' - 1 rho^T} g_{k+1}(Z) ),  pi: C^5 -> C^5 / U^perp,
       k = 0: pi(rho) = -pi(colsum X');   k = 3: Gamma_3(Z) rho in U^perp (the Phi-type condition of L5).
 10.1 EL IS NOT A LEMMA ABOUT DELETABLE ROWS:
   (i) [rigorous, hand] M = C e_0 u^T, u = e_1 - e_2: T_1 = {sum t = 0, sum_{i=1,2,3} <t_i,u> = 0} (cof_{0j} = 24, cof_{ij} = 24 - 6 y u_j), so
       Omega = C^5, while A(Cu) = {s_1 = s_2}.  (Not saturated.)
   (ii) [EXACT, reg2/el_exact.py] EL-SAT is false too: (2,2|2) member mu = (0,1,2,3), S = C Y0 (Y0 = B_0 + 2B_1 - B_4 + 3B_5 inside M_1),
       e(S) = 1, U = (C(S)+C1)^perp 3-dim, M_S = S (+) e_1 (x) U is level (exact identity), dim T_1 = 13, Omega = C^5, dim A(U) = 2.
   (iii) [numerical, reg2/el_test.py and the sweep reg2/el_sweep.py] EL-SAT holds for every 2- and 3-dim S tested inside the
       DR families ((2,1,1|2) (ii) generic and D, (iii), (2,2|2) incl. a 0/1 member, (3,1|2) generic and isotropic, M*_2; 64 tests, 0 violations,
       always Omega = A(U)), fails for every 1-dim S there, and fails for 2-dim S inside the Type F kernel M_L080_col0 (Omega = C^5, dim A(U) = 1).
   So EL is a property of the 6-dim spaces (and of large enough pieces of the DR families), not of the deletable-row shape: a proof must use
   dimension 6 / maximality, i.e. it is not easier than the classification. What (b)-(c) do give: EL for a given M is the statement that the
   affine vector field K -> X' - K D_rho is "normal-constant" for the functions <u, G(K)> on J'_3 + S'.
STATUS 20:45: target 1 answered negatively (EL false as a general deletable-row lemma; exact counterexample to the saturated form). Moving to X1'.

## 11. Round 4, TASK X1': the NC line-spanned patterns
 Method (new, uniform, exact): reg2/gb/gen_rank.py FAMILY r K SEED.  The FO equations are linear in t = (X; rho): coefficient matrix A(params)
 (rows = y-monomials, 25 columns). K minors of size r = 16 are chosen GREEDILY at random rational parameter points (independent rows, then
 independent columns; exact Fractions), computed by Singular (det of submat over Q[params]); if they generate (1) then rank A >= 16, i.e.
 dim T_1 <= 9, for EVERY member, hence FO2 bound <= 8 (8.1(a)). If they cut out finitely many points, each point gets an exact certificate
 (reg2/nc_cert.py: exact rank of the full FO matrix over Q or Q(sqrt -3)). No pivots, no localisation, no charts in t; spanning sets allowed.
 11.1 (3|2,1) [hand + exact]. Row 0: U = {1,m}^perp; column c: V (2-dim), column c': C x', V perp x'. Incidences: U vanishes at a column iff
     m ~ 5e_c - 1. (a) m ~ 5 e_c - 1, x'_0 = 0, V = x'^perp cap 1^perp (determined by x' in P^1); (b1) V = {x_0 = 0}, x'_0 = 0: impossible
     (x' in {x_0=0, sum=0} cap span(e_0,1) = 0); (b2) V = {x_0 = 0, sum = 0}, m ~ 5 e_c' - 1, x' ~ (-3,1,1,1): one space.
     Level for all parameters [hand: rows i,k >= 1 live in columns c, c' only; the {0,i,k} terms sum to -u_c' [(sum v)(sum x') - <v,x'>] = 0;
     three rows >= 1 never fit]. EXACT: (a) chart x' = (0,1,p,-1-p): 25 greedy minors generate (1) (seed 2); x' = (0,0,1,-1): dim T_1 = 9;
     (b2): dim T_1 = 9.  Numerically (e, dim E_0, dim Omega, dim T_1, FO2) = (3, 7, 2, 9, 7), Omega = span(1, e_c) (NC type).
 11.2 (2,1|3) [hand + exact]. V = 1^perp (all of it) forces both row parts to vanish at column c: M = e_0 (x) (u^perp cap H_c) (+) C e_1 u^T (+)
     1^perp (x) e_c, u in P(H_c) (2 parameters; isotropic u included). Level for every u [hand: rows 2, 3 live in column c only; the {0,1,k}
     terms carry (sum u')(sum u) - <u',u> = 0]. EXACT: chart u_0 = 1 (S_4 symmetry of the other columns): 40 greedy minors cut out 11 rational
     points (dim 0), and at each of them dim T_1 = 9 exactly (nc_cert.py). So dim T_1 <= 9 for every member. Numerically (3,7,2,9,7), NC type.
 11.3 (3|1,1,1) [hand + exact]. Row 0: U = {1,m}^perp; columns c1,c2,c3: x1, x2, x3 pairwise orthogonal.
     (a) no column with m ~ 5e_c - 1: all x_k in {x_0 = 0, sum = 0} pairwise orthogonal forces x1 = x2 = x3 = l isotropic; then the coefficient
         of z1 z2 z3 in P_3 (rows 1,2,3, a rank-one block l z^T) is 6 l_1 l_2 l_3 = 6 != 0: EMPTY.
     (b) m ~ 5 e_c1 - 1, (x2)_0 = (x3)_0 = 0: (b-i) x2, x3 an orthogonal pair spanning {x_0=0, sum=0}, x1 ~ (3,-1,-1,-1);  (b-ii) x2 = x3 = l
         isotropic, x1 = alpha (3,-1,-1,-1) + beta l, and the z1z2z3 coefficient of P_3 is 2*3 beta, so beta = 0.
     EXACT: (b-i) chart x2 = (0,1,p,-1-p): 25 greedy minors generate (1) (two seeds); x2 = (0,0,1,-1): dim T_1 = 9; (b-ii) over Q(sqrt -3):
     level identity, dim T_1 = 9.  Numerically (3,7,2,9,7), Omega = span(1, e_c1).
 So (3|2,1), (2,1|3), (3|1,1,1) satisfy (S6-FO2) with dim T_1 <= 9 for EVERY member (FO2 bound <= 8; numerically 7).
STATUS 20:54: X1' -- (3|2,1), (2,1|3), (3|1,1,1) closed exactly (section 11). Next: (2,1|2,1), (2,1|1,1,1), (1,1,1|2,1).
 11.4 (2,1|2,1) [hand + exact]. Rows 0 (U_0, 2-dim), 1 (C u); columns c = 4 (V, 2-dim), c' = 3 (C x'), V perp x', U_0 perp u.
     Incidences (V vanishes at <= 1 row):
     (V0) V = {x_0 = 0, sum = 0}: u_4 = 0; x' in V^perp cap 1^perp = C(3,-1,-1,-1), so U_0 vanishes at column 3 and u_3 = 0:
          u in H_34 := {w_3 = w_4 = 0, sum = 0}, U_0 = {w_3 = 0, sum = 0, <w,u> = 0}  (1 parameter).
     (V1) V = {x_1 = 0}: U_0 vanishes at 4, x' ~ (-1,3,-1,-1), so U_0 = H_34 and u in span(e_3, e_4, 1) with u_3 = 0, sum 0: u = 0. EMPTY.
     (Vn) V vanishes at neither row 0 nor row 1: U_0 vanishes at 4, u_4 = 0, and for column 3:
          (i) x' = (0,0,1,-1), V = x'^perp cap 1^perp, U_0 = u^perp cap H_4, u in H_4 (2 parameters);
          (ii) x'_0 = 0, u_3 = 0: x' in {x_0 = 0, sum = 0}, V = x'^perp cap 1^perp, u in H_34, U_0 = u^perp cap H_4 (2 parameters);
          (iii), (iv) U_0 vanishing at column 3 forces U_0 = H_34 and then u = 0: EMPTY.
     Level for all parameters in V0, Vn-i, Vn-ii [exact: no level equations]. Charts: u_0 = 1 (S_3 symmetry of the columns 0,1,2).
     EXACT dim T_1 <= 9 for EVERY member: V0: 40 greedy minors generate (1); Vn-i: minors cut out 10 rational points, each dim T_1 = 9 exactly;
     Vn-ii: main chart (s,p) leaves the curve s = 0 (separately: 40 minors generate (1)) and 10 points (one is (s,p) = (-1, omega), conjugate by
     complex conjugation), each dim T_1 = 9 exactly (Q resp. Q(sqrt -3)); the sub-family x' = (0,0,1,-1): 40 minors generate (1).
     Numerically all members (3,7,2,9,7), NC type (Omega = span(1, e_c) for the column carrying V... in V0: span(1, e_3)).
     Logs: reg2/gb/gen_rank.py (families 2121V0, 2121Vni, 2121Vnii, 2121Vnii_s0, 2121Vnii_xinf), reg2/gb/runs/nc_cert_2121.log.
STATUS 21:00: (2,1|2,1) closed exactly. Remaining NC patterns: (2,1|1,1,1), (1,1,1|2,1). Local census E (20 starts/pattern) running.
 11.5 (1,1,1|2,1) [hand + exact]. Rows 0,1,2: C u_0, C u_1, C u_2 (pairwise orthogonal); column 4: V (2-dim); column 3: C x', V perp x'.
     (A) V vanishes at a row r in {0,1,2} (r = 0 by symmetry): V = {x_0 = 0, sum = 0}, x' ~ (3,-1,-1,-1) (no zero), so all u_i vanish at column 3,
         and u_1, u_2 at column 4: u_1, u_2 in H_34. (A1) u_1, u_2 a non-isotropic orthogonal pair: u_0 ~ (1,1,1,0,-3); (A2) u_1 = u_2 = l
         isotropic, u_0 = alpha (1,1,1,0,-3) + beta l: the y0y1y2 coefficient of P_3 is e(u_0, l, l) = 2 <u_0, l o l> = 6 beta, so beta = 0
         (= the isotropic point of A1).
     (B) V vanishes at none of rows 0,1,2: all u_i in H_4; Z := {i <= 2 : x'_i = 0}. (B0) Z empty: u_0 = u_1 = u_2 = l isotropic in H_34, and the
         y0y1y2 coefficient 6 l_0 l_1 l_2 != 0: EMPTY. (B1) Z = {0}: u_1, u_2 in H_34 orthogonal, u_0 ~ (1,1,1,-3,0) (isotropic variant forces
         beta = 0 as in A2), x' in {x_0 = 0, sum = 0}, V = x'^perp cap 1^perp. (B2) Z = {0,1}: x' = (0,0,1,-1), u_2 in H_34, u_0 perp u_1 in
         u_2^perp cap H_4 = span((1,1,1,-3,0), c3(u_2)); its level variety (exact, minAssGTZ of the 3 level equations) is q = 0, s = -1, s = 0.
     EXACT: A1 chart u_1 = (1,s,-1-s,0,0) (S_3 symmetry): 40 greedy minors generate (1).  B1 chart (s,p): minors cut out 5 points (two over
     Q(omega)), each dim T_1 = 9 exactly.  B2 (with its level equations): minors cut out 8 points, each dim T_1 = 9 exactly (nc_cert_11121.log).
     [CORRECTED R5 21:36: gen_rank.py added the level equations as 'I=I+poly' WITHOUT parentheses, which Singular parses term by term
      (each monomial became a generator). Only B2 had level equations. Rerun with 'I=I+(poly)': the minors leave 12 points (the 8 above and
      (s,q) = (-1,4), (-1,1), (-1,-1/2), (-1,-2)); all 12 have dim T_1 = 9 exactly. The conclusion for B2 stands, now with a correct input.]
     Numerically all members (3,7,2,9,7).  So (1,1,1|2,1) satisfies dim T_1 <= 9 for every member.
 11.6 Status of TASK X1': DONE (exact, dim T_1 <= 9 for every member, so FO2 <= 8): (3|2,1), (2,1|3), (3|1,1,1), (2,1|2,1), (1,1,1|2,1).
     NOT DONE: (2,1|1,1,1) (hand case split started: per x-column four incidence types A/B/C/D, at most one D-column (x ~ (0,0,1,-1));
     the y_{c1} y_{c2} y_{c3} coefficient of P_3 is e(x1,x2,x3) = 2 T(x1,x2,x3), so T(x1,x2,x3) = 0 is a level condition).
     Every line-spanned pattern with at least one known 6-dim member is now settled for the gap except (2,1|1,1,1).
STATUS 21:08: X1' five of six patterns closed exactly; (2,1|1,1,1) left; census E local run (20 starts/pattern) finishing; CE-1 queued.

## 12. Round 4: census E, line-spanned part (local calibrated run; full run queued as CE-1)
 reg2/census_e.py SEED SLICE NSLICES NSTARTS (wraps linespan.solve; each hit re-checked at fresh points; invariants at tolerances 1e-6 and 1e-9;
 candidates = no full free row and FO2 >= 9 at both). Local run: 45 patterns x 20 starts (2 slices, ~6 min each; logs reg2/census_e_r4/ce_slice*.log).
 Calibration (patterns with exact families): (3|3) 20/20, (3|1,1,1) 10/20, (3|2,1) 14/20, (2,1|3) 2/20, (2,1|2,1) 1/20, (1,1,1|3) 4/20,
 (1,1,1|2,1) 7/20, (3,1|2) 13/20, (3,1|1,1) 2/20, (2,2|2) 12/20, (2,1,1|2) 5/20 -- every exactly known pattern is re-found.
 NEW patterns with 6-dim members (the round-2 list from 2 starts per pattern was incomplete): (2,2|1,1) 6/20, (1,1,1,1|2) 6/20,
 (1,1,1|1,1,1) 1/20, and (2,1|1,1,1) 1/20.
 Invariants of all 104 hits [numerical]: 102 x (dim Omega, dim T_1, FO2) = (2, 9, 7) and 2 x (3, 10, 8) (both in (2,2|1,1)), identical at the
 two tolerances; no full free row; NO CANDIDATE.  So TASK X1 now has four open patterns: (2,1|1,1,1), (2,2|1,1), (1,1,1,1|2), (1,1,1|1,1,1).
STATUS 21:12: RESULT ROUND 4 block on top (with the round-3 theorems and their inputs for verify2); census E section 12 written.
 11.7 (1,1,1,1|2) [hand; exact in part]. Rows 0..3: C u_i (pairwise orthogonal), column 4: V (2-dim).
     (B) V vanishes at no row: all u_i in H_4 (3-dim nondegenerate). Pairwise orthogonal nonzero vectors: the non-isotropic ones N span a
         nondegenerate space, the isotropic ones lie in a totally isotropic subspace of its complement; with |N| + |I| = 4 this leaves
         |N| = 1 (u_1 = u_2 = u_3 = l isotropic) or |N| = 0 (all = l). P_3 (y_i y_j y_k coefficient e(u_i,u_j,u_k) = 2T) forces sum l^3 = 0, so
         l ~ chi_1 = (1,i,-1,-i); |N| = 1: u_0 perp chi_0, chi_1, chi_2 gives u_0 ~ chi_1, contradiction; |N| = 0: the y0y1y2y3 coefficient
         perm_4(l,l,l,l) = 24 prod l_j = -24 != 0. EMPTY.
     (A) V = {x_0 = 0, sum = 0} (r = 0): u_1,u_2,u_3 in H_4, u_0 in 1^perp. |N| = 3: u_0 ~ (1,1,1,1,-4), (u_1,u_2,u_3) an orthogonal frame
         with T(u_1,u_2,u_3) = 0 (level iff T = 0, numerically: the T != 0 frame is not level) -- the same variety as (2,1,1|2)(ii);
         |N| = 2 impossible; |N| = 1: u_2 = u_3 = l, u_0 = alpha g + beta l, and the y0y2y3 / y1y2y3 coefficients force beta sum l^3 = 0 and
         <u_1, l o l> = 0, so beta = 0 (if sum l^3 = 0 then u_1 ~ l): inside the |N| = 3 parametrisation (b = u_1, c = l, a = cross4 ~ l);
         |N| = 0: u_1 = u_2 = u_3 = chi_1 and P_3 / P_4 force u_0 = g: ONE space, EXACT over Q(i): level, dim T_1 = 9 (nc_cert.py 1111pt).
     Numerically every member (4 random frames with T = 0, the D-type and SIGMA-type frames): (e, dim E_0, dim Omega, dim T_1, FO2) =
     (4, 7, 2, 9, 7), Omega = span(1, e_4) -- no special locus (consistent with EL: the deletable row 0 has U = C g, A(U) = span(1, e_4)).
     EXACT for the main family: reg2/gb/gen_rank2.py (charts b_0 = 1, c_0 = 1 / c_1 = 1; minors chosen at numerical family points) RUNNING
     at the end of the round (see the final report / next STATUS).
     [21:28] gen_rank2.py chart (b_0 = 1, c_0 = 1), 30 minors chosen at numerical family points: the ideal (minors + 6 level equations) has
     dimension 2 and minAssGTZ printed primes that do NOT contain <b,c> (checked: reduce(<b,c>, P) != 0) -- an inconsistency I could not
     resolve in the time left (suspect output truncation or a script error). The chart-1 run was stopped. So the main (1,1,1,1|2)(A) family is
     [numerical] only: (2,9,7) at every tested member.  TODO: redo with the gen_dr211d.py Omega/E_0 pipeline (it is the (2,1,1|2)(ii) variety with
     the frame moved to rows 1-3 and g in row 0; the expected answer is dim T_1 = 9 everywhere, with NO special locus).
STATUS 21:29: end of round 4. CE-1 is running on the queue (6 slices, started by the coordinator). Final report sent.

# ROUND 5 (reg2, start 21:26 UTC; memory rule: own jobs ulimit -v 2000000, one job > 0.5 GB at a time).
# Targets: (1) (2,1|1,1,1), (2,2|1,1), (1,1,1|1,1,1); (2) (1,1,1,1|2)(A) exactly + the gen_rank2 inconsistency; (3) CE-1; (4) structure route.
STATUS 21:27: round 5 started with (2,2|1,1): hand split gives types B/C/D per column (type A impossible: e_c - 1/5 would be an isotropic
 element of U_0), (B,C) impossible; families BB (1 parameter) and BD (2 parameters) up to row/column symmetry.

## 13. Round 5: the remaining line-spanned patterns
 13.1 (2,2|1,1) [hand + EXACT].  Rows 0, 1: 2-dim parts U_0, U_1; P_2 forces U_1 = (U_0 + C1)^perp (and U_0^perp = U_1 + C1).
     Columns c, c': C x, C x', x perp x'. Per column the incidence types are A (U_0 and U_1 vanish at c), B (U_0 vanishes, x_1 = 0),
     C (U_1 vanishes, x_0 = 0), D (x_0 = x_1 = 0, x ~ (0,0,1,-1)).  U_0 vanishes at c <=> e_c - 1/5 in U_1;  U_1 vanishes at c <=> e_c - 1/5 in U_0.
     A is impossible (e_c - 1/5 would lie in U_0 and be orthogonal to U_0, but <e_c - 1/5, e_c - 1/5> = 4/5); (B,C) is impossible
     (<e_c' - 1/5, e_c - 1/5> = -1/5 != 0); (D,D) impossible (<d,d> = 2). Up to the row swap 0 <-> 1 (B <-> C) and c <-> c':
     BB: U_0 = span(e_0-e_1, e_0-e_2), U_1 = span(5e_3 - 1, 5e_4 - 1), x perp x' in {x_1 = 0, sum = 0}  (1 parameter);
     BD: U_1 = span(5e_3 - 1, v), v = (1, v1, v2, 0, -1-v1-v2), U_0 = (U_1 + C1)^perp, x = (2,0,-1,-1) in column 3, x' = (0,0,1,-1) in column 4.
     Both level for all parameters [exact: no level equations].
     BB: the WHOLE curve has dim T_1 = 10 (Omega = span(e_3, e_4, 1_{012})): EXACT dim T_1 <= 10 (gen_rank 2211BB r = 15: 30 minors leave only
         p = -1/2, where dim T_1 = 10 exactly; the point x = (0,0,1,-1): dim T_1 = 10) and rank q >= 3 for EVERY member (gb/p2211_rank.py:
         unique lifts of rho = e_3, e_4 exist for all p, Gram of q on span(4 d_1, tau, t_3, t_4), 3x3 minors + elimination ideal = (1) in both
         x-charts and both pivot charts); exact rank 4 at p = -1/2 and x = (0,0,1,-1). So FO2 bound = 8 on BB.  [These are the census (3,10,8) hits.]
     BD: gen_rank 2211BD (40 minors) leaves 8 points; exactly: v = (1,0,-1,0,0): (9, rank 3, 7); the other seven: dim T_1 = 10, rank q = 4,
         bound 8 (reg2/p2211_pts.py). Elsewhere dim T_1 <= 9.
     => (2,2|1,1): every member has FO2 bound <= 8 [EXACT].
STATUS 21:32: (2,2|1,1) closed exactly (BB curve (10,4,8) certified by lifts; BD 8 special points certified). Next (2,1|1,1,1), (1,1,1|1,1,1).
 13.2 THE gen_rank2 INCONSISTENCY OF 11.7 IS EXPLAINED: same parenthesisation bug (level equations entered term by term), so the "ideal" was not
     the family ideal; fixed in gen_rank.py and gen_rank2.py ('I=I+(poly)'). Every other gen_rank family had NO level equations, so their
     certificates are unaffected.
 13.3 (1,1,1,1|2)(A) [EXACT, char 0]: Omega/E_0 pipeline (gb/gen_1111d.py + gb/dr1111_common.py, cloned from DR211-ii; row 0 = g deletable, so
     d_0 in E_0; pivots x04 (g), x10 (b), x2jc (c), x3ja (a, localised), block x14,x24,x34 for {V, d_0} (determinant -3/4)). Omega normalisation =
     complement of span(1, e_4): rho_4 = 0, rho_0+..+rho_3 = 0, rho_jr = 1.  Singular over Q (log gb/runs/dr1111q.log): all 48 Omega-tests UNIT,
     all 156 E_0-tests UNIT (components (g) and (d), charts b_0 = 1, c_0 | c_1 = 1, a_ja != 0); calibrations NON-unit (rho = e_4: 12 of 12; d_0 pivot
     released: 3 of 3); mod 65521 (msolve) identical.  So dim T_1 <= 9 for EVERY member: NO special locus (unlike (2,1,1|2)(ii), as EL predicts).
     With 11.7 (case B empty, the degenerate sub-cases, the exact point over Q(i)): (1,1,1,1|2) is CLOSED: FO2 bound <= 8 for every member.
 13.4 (2,1|1,1,1) [hand + EXACT]. Per x-column type A/B/C/D as in 11.6 (A: U_0 and u vanish at c_k; B: U_0 vanishes, x_k1 = 0; C: u vanishes,
     x_k0 = 0; D: x_k = (0,0,1,-1)); at most one D, at most two A/B (|Z0| <= 2). Twelve type triples; hand eliminations:
       |Z0| = 2 (U_0 = {w_Z0 = 0, sum = 0}, u in span(1, e_Z0)): AAC, AAD, ABC give u = 0; BBC: x1 = x2 isotropic forced and T(x1,x2,x3) = 3 != 0;
           BBD: x1, x2 both ~ (2,0,-1,-1), not orthogonal; ABD survives as ONE space;
       |Z0| = 1: BCC (T = 3 != 0 or B violated), BCD (x1 ~ (2,0,-1,-1) not perp x2 ~ (0,2,-1,-1)) empty; ACC (u = e_d1 - e_d2, x1 = (3,-1,-1,-1),
           x2 perp x3 in {x_0 = 0}; isotropic variant forced to beta = 0) and ACD (x = (3,-1,-1,-1), (0,2,-1,-1), (0,0,1,-1), u in span on the
           columns d1, d2, c3) survive (1 parameter each);
       |Z0| = 0: CCC (T(l,l,l) = 3 != 0), CCD (not orthogonal) empty.
     (The y_c1 y_c2 y_c3 coefficient of P_3 is e(x1,x2,x3) = 2 T(x1,x2,x3) for pairwise orthogonal sum-zero x_k: a level condition.)
     All three survivors level for all parameters [exact: no level equations]. EXACT: ACC: 30 greedy minors generate (1); ACD: minors leave
     s = -1, where dim T_1 = 9 exactly; the point u = (0,1,0,0,-1) is s = 0 after swapping the columns d1, d2; ABD and ACC at x2 = (0,0,1,-1):
     dim T_1 = 9 exactly.  Numerically all (3,7,2,9,7).  => (2,1|1,1,1) CLOSED (dim T_1 <= 9 for every member).
STATUS 21:38: (2,2|1,1), (1,1,1,1|2), (2,1|1,1,1) closed exactly; gen_rank parenthesis bug found and fixed (only (1,1,1|2,1)B2 affected; recertified).
 Next: (1,1,1|1,1,1), CE-1, structure route.
 13.5 (1,1,1|1,1,1): CE-1 0 hits / 200 starts, my targeted runs 0 / 260 (the local census had 1 / 20, not saved). Hand facts: the only P_3
     conditions are T(u_0,u_1,u_2) = 0 and T(x1,x2,x3) = 0 (the mixed y_u y_u y_x and y_u y_x y_x coefficients are -2(x_k(i)+x_k(j)) u_i(c_k) u_j(c_k)
     and -2 x_k(i) x_l(i)(u_i(c_k)+u_i(c_l)), which vanish by the incidences); P_4 gives x_k(3) u_0(c_k) u_1(c_k) u_2(c_k) = 0 and more.
     NOT closed (members rare; full case split over the incidence supports still to do).
 13.6 NEW PATTERN from CE-1: (2,1,1|1,1) has 8 hits / 200 starts: 5 x (3,10,8), 3 x (2,9,7) [numerical]. NOT treated yet (the hand split starts
     from U_0 vanishing at c <=> e_c - 1/5 in W := U_0^perp cap 1^perp, the plane containing the orthogonal pair u_1, u_2).
 13.7 Structure route (target 4), first experiment (reg2/lev35.py, holomorphic Gauss-Newton for 3x5 level spaces S, F_3(J+Y) = 60):
     random 3-dim 3x5 level spaces are found at every start, have defect e = 4 and are NOT line-spanned (no single-row or single-column
     elements at all). For a 6-dim space with a deletable row, M = S (+) e_i (x) (C(S)+C1)^perp forces dim S - e(S) = 2, i.e. (dim, e) in
     {(3,1), (4,2), (5,3)} -- the 3x5 analogue of the defect problem. So "deletable-row 6-dim spaces are line-spanned" is a statement about these
     constrained 3x5 spaces only; it can be tested by a search with the defect constraint built in (drsearch.py does this in the 4x5 picture).
 13.8 CE-1 (queue, 200 starts/pattern, 41 of 45 patterns at 21:43): 1142 hits, (2,9,7) x 1093 and (3,10,8) x 49 (in (2,1,1|1,1), (2,2|1,1) BB,
     (3,1|1,1)), no full free row, NO CANDIDATE. Patterns with hits: those of section 12 plus (2,1,1|1,1).
STATUS 21:47: (1,1,1|1,1,1) and the new (2,1,1|1,1) left open; CE-1 nearly finished, no candidate. Writing the final report.
 13.9 (2,1,1|1,1) [hand + EXACT, partial]. Rows 0 (U_0, 2-dim), 1, 2 (u_1, u_2); columns c = 3, c' = 4 (x, x'). W := U_0^perp cap 1^perp
     (2-dim) contains the orthogonal pair u_1, u_2 (if u_1 ~ u_2, an isotropic line, W is not determined by them -- see IV-iso).
     U_0 vanishes at column k  <=>  f_k := e_k - 1/5 in W.  Cases by the set of columns where U_0 vanishes:
     (I) both: W = span(f_3, f_4), U_0 = {w_3 = w_4 = 0}; the only elements of W vanishing at 3 (resp. 4) are v3 = f_3 + 4 f_4, v4 = 4 f_3 + f_4,
         <v3,v4> = 3, <v3,v3> = 12; x, x' with zeros at rows 1, 2 would be parallel and non-isotropic: the only survivor is
         (I-a): u_1 = (-1,-1,-1,0,3), u_2 = (-1,-1,-1,4,-1), x = (1,-2,0,1), x' = (1,0,0,-1): EXACT (9, rank 3, 7).
     (IV) neither (x_0 = x'_0 = 0): per column the options (a) u_1, u_2 both vanish, (b) u_1 vanishes and x(2) = 0, (c) u_2 vanishes and
         x(1) = 0; (b,b), (b,c), (c,c) contradict x perp x'. Survivors up to symmetry:
         (a,a): u_1, u_2 orthogonal basis of H_34, U_0 = span(5e_3 - 1, 5e_4 - 1), x perp x' in {x_0 = 0} (2 parameters). WHOLE family has
             dim T_1 = 10: EXACT dim T_1 <= 10 (15x15 minors leave 9 points, each (10, rank 4, 8); sub-family x = (0,0,1,-1): minors generate (1))
             and rank q >= 3 for every member (gb/p21111aa_rank.py: unique lifts of e_3, e_4, Gram minors = (1) in all 4 pivot charts;
             x = (0,0,1,-1): reg2/p21111x0.py, gcd of the principal 3x3 minors over Q(s) is a constant). FO2 bound 8.  [census (3,10,8) hits]
         IV-iso: u_1 = u_2 = l = (1,w,w^2,0,0); P_3 forces U_0 perp l o l, so U_0 = span((1,1,1,-3,0),(0,0,0,1,-1)); x perp x' free (1 parameter):
             dim T_1 <= 10 (minors with w^2+w+1 = 0 leave 6 points, each (10, rank 4, 8) over Q(sqrt -3); x = (0,0,1,-1): (10,4,8)); rank q >= 3
             everywhere (gb/p21111iso_rank.py, lifts + Gram minors = (1)). FO2 bound 8.
         (a,b): u_1 in H_34, u_2 = (1,1,1,0,-3) + q c3(u_1), x = (0,1,-2,1), x' = (0,1,0,-1), U_0 = {1,u_1,u_2}^perp; its level variety is
             q = 0, s = -1, s = 0 (exact); minors (with the level equations, correctly bracketed) leave 12 points: eight (9, rank 3, 7), four
             (10, rank 4, 8) (reg2/p21111_pts.py ab; the point (0, omega) is level -- sympy's expand needed simplify). FO2 bound <= 8.
     (II)/(III) U_0 vanishes at exactly one of the two columns: NOT YET DONE (hand split started: f_3 in W, x'_0 = 0, at least one of u_1, u_2
         vanishes at column 4; the elements of W vanishing at a given column form a line).  CE-1 found no hit with U_0 vanishing anywhere.
     So (2,1,1|1,1): every member in cases I and IV has FO2 bound <= 8 [exact]; cases II/III open.
STATUS 21:55: (2,1,1|1,1) cases I and IV closed exactly (incl. the whole (3,10,8) curve and the isotropic sub-family); II/III open.
 13.10 (2,1,1|1,1) cases II/III [hand + EXACT] -- (III) is (II) with the two x-columns swapped. (II): f_3 in W, f_4 not in W, x'_0 = 0; the elements
     of W vanishing at column k form a line L_k (L_3 = C w after normalising W = span(f_3, w) with w_3 = 0; L_4 = C(5 w_4 f_3 + w)); x' cannot vanish
     at rows 1 and 2, so (rows 1 <-> 2) u_1 in L_4.
     (II-1) u_2 in L_4 too: u_1 = u_2 = l isotropic, W = span(f_3, l); if l(3) = 0 then l in H_34 and P_3 (coefficient 2<u, l o l>) forces
            U_0 to be 1-dim; if l(3) != 0 then x ~ (1,0,0,-1) and U_0 = {1, e_3, l}^perp must be perp l o l, i.e. l o l in span(1, e_3, l), which
            forces l = 0. EMPTY.
     (II-2) u_2 not in L_4: x' = (0,1,0,-1), x_1 = x_3. Column 3: both u in L_3 contradicts u_1 in L_4, u_2 not; (gamma) u_2 = w, x = (1,0,-1,0) forces
            w isotropic and then U_0 perp w o w, impossible as above; (delta) x(1) = x(2) = 0 gives x = 0.  Survivor (beta): u_1 = w in H_34,
            x = (-2,1,0,1); u_2 perp w in W gives u_2 = 5e_3 - 1 (w non-isotropic) -- the isotropic w forces the extra coefficient beta = 0 by P_3 --
            so ONE 1-parameter family: U_0 = {sum = 0, w_3 = 0, perp w}, u_1 = w = (1,s,-1-s,0,0), u_2 = 5e_3 - 1, x = (-2,1,0,1), x' = (0,1,0,-1).
            Level for all s [exact]; gen_rank 21111II: minors leave s = 0, where dim T_1 = 9 (rank 3, bound 7) exactly. dim T_1 <= 9 everywhere.
     => (2,1,1|1,1) is CLOSED: every member has FO2 bound <= 8 [exact].
STATUS 21:57: (2,1,1|1,1) closed exactly (cases I-IV). Of the line-spanned patterns with known members only (1,1,1|1,1,1) is open.
 13.11 CE-1 FINISHED (queue run, reg2/census_e_q/ce_*.log; 45 patterns x 200 starts): 1142 hits in 15 patterns, (2,9,7) x 1093, (3,10,8) x 49,
     identical at tolerances 1e-6 / 1e-9, no full free row, NO CANDIDATE. The 15 patterns with hits are exactly
     (3|3), (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1), (1,1,1|3), (1,1,1|2,1), (1,1,1,1|2), (3,1|2), (3,1|1,1), (2,2|2), (2,2|1,1),
     (2,1,1|2), (2,1,1|1,1) -- ALL FIFTEEN ARE NOW CLOSED EXACTLY ((S6-FO2) or SP8 for the gap). (1,1,1|1,1,1): 0 / 200 here (1 / 20 locally in
     round 4, 0 / 260 targeted). The other 29 patterns: 0 hits in 200 starts each [numerical evidence that they have no 6-dim member].
 13.12 Consequence (for the coordinator): every LINE-SPANNED 6-dim 4x5 level space in a pattern with a found member satisfies "every 5x5 level
     space containing it has dim <= 8" [exact]; the open line-spanned items are (1,1,1|1,1,1) and the emptiness of the 29 hit-free patterns.
     (S6-FO2) for NON-line-spanned 6-dim spaces is untouched by this table (structure route, 13.7).
STATUS 21:59: CE-1 folded in (all 15 hit patterns closed). Final report.

# ROUND 6 (reg2, start ~21:57 UTC). Targets: (1) structure route via 3x5 spaces with dim S - e(S) = 2; (2) (1,1,1|1,1,1); (3) the 29 hit-free
# patterns; (4) second-generator certificate of the (3,10,8) curves.
## 14. Structure route: deletable-row 6-dim spaces are NOT all line-spanned
 14.1 Setting [rigorous]: M = e_0 (x) U (+) S with row 0 meeting M only in U (deletable row, strong sense), S = M cap {row 0 = 0} = a 3x5 level space
     (rows 1..3), U inside (C(S)+C1)^perp (Z3), so 6 = dim M <= dim S + 4 - e(S); equality iff U is saturated; dim S - e(S) >= 3 would give a
     7-dim 4x5 level space (saturate U).  So for 6-dim M: (dim S, e(S)) = (6-u, 4-u), u = dim U in {1,2,3}, or a 7-dim space exists.
 14.2 Search (reg2/dr35.py SEED u NSTARTS: holomorphic Gauss-Newton in random Grassmannian charts for U inside 1^perp and S inside the
     sum-zero 3x5 matrices; each hit: e(S), raw and sparse-limit line-span test of S, (dim Omega, dim T_1, FO2) of M) [numerical]:
     u = 3 (S = (3,1)): 250 starts -> 24 hits: 17 line-spanned, 7 NOT line-spanned; FO2 (9,3,7) x 5, (10,4,8) x 16, (11,5,8) x 3.
     u = 2 (S = (4,2)), u = 1 (S = (5,3)): running (section 14.4).
 14.3 The two non-line-spanned shapes found (sparse limits, level error 1e-13 after rounding):
     (BLOCK) S = C e_2 m^T (+) { x e_a^T + a (J x) e_b^T : x in V },  V = {x : x_0 = 0, sum x = 0} (rows 1..3), J x = (x_2-x_3, x_3-x_1, x_1-x_2)
         (the rotation of V: <x, Jx'> = -<Jx, x'>, which is exactly P_2 = 0 on the block), a in C* a free scale, m_a = m_b = 0,
         U = {1,m}^perp.  Example dr35_u3_s1_3 (columns a,b = 1,4), dr35_u3_s41_56 (columns 3,4): (dim Omega, dim T_1, FO2) = (3, 10, 8).
         Its single-row element e_2 m^T makes it a split pair: SP8(b) applies when <m,m> != 0 (true in both examples).
     (RANK-ONE) S contains (e_1 - e_3) (x) (m o m) with m = (1,0,w^2,0,w) isotropic of 3-column support, plus e_2 m^T and a single-column
         element; U = {1,m}^perp (dr35_u3_s41_29): (3,10,8). This is the isotropic split case of SP8 (not covered by SP8; FO2 = 8 numerically).
     CONCLUSION: the claim "every 6-dim deletable-row space is line-spanned" is FALSE (numerically, with explicit sparse examples). A structure
     theorem must allow at least rank-one elements x (x) v (|supp x|, |supp v| >= 2) and the skew two-column blocks above. No hit violates
     (S6-FO2): FO2 <= 8 throughout.
STATUS 22:01: structure route -- line-spanned claim refuted numerically (BLOCK and RANK-ONE shapes); u = 2, 1 censuses running.
 14.4 Census results [numerical]: u = 2 (S = (4,2)): 250 starts -> 5 hits, all line-spanned, (9,3,7) x 4, (10,4,8) x 1; u = 1 (S = (5,3)): 200 starts
     -> 1 hit, line-spanned, (9,3,7). Hit rates (10%, 2%, 0.5%) are low for u = 2, 1: those censuses are thin (not a classification).
 14.5 THE BLOCK FAMILY, EXACT [hand + exact]: for every (t, a),
         M_B(t,a) = e_0 (x) {1,m}^perp (+) C e_2 m^T (+) { x e_1^T + a (Jx) e_4^T : x in V },   m = (t, 0, -1-t, 1, 0),
     V = {x : x_0 = 0, sum = 0}, J x = (0, x_2-x_3, x_3-x_1, x_1-x_2), is a 6-dim LEVEL space [exact: no level equations, gb/blockfam.py];
     for a != 0 it is NOT line-spanned (exact at (t,a) = (1,1): single-row parts (3,0,1,0), single-column parts all 0; reg2/block_exact.py:
     (dim T_1, rank q, bound) = (10, 4, 8)).  P_2 on the block is -<x, a Jx> = 0 because J is skew -- this is the mechanism.
     (S6-FO2) on the whole family [exact]: rank q >= 3 for every member with t != 0 (gb/pblock_rank_all.py: unique lifts of rho = e_1, e_4 and
     Gram minors = (1)); dim T_1 <= 10 except t in {0, -1} and (t,a) = (1,0) (gen_rank blockall, after skipping degenerate random points); at
     t = 0, -1 the vector m is a two-column vector (SP8(a)), and a = 0 is line-spanned ((3,1|2), section 9.7). Isotropic m (t = omega): also
     separately (gb/pblock_rank.py, gen_rank blockiso, reg2/block_iso_a0.py). So every level space containing a BLOCK member has dim <= 8.
 14.6 THE RANK-ONE SPACE, EXACT (reg2/rankone_exact.py, over Q(sqrt -3)): M_R = e_0 (x) {1,m}^perp (+) C e_2 m^T (+) C (0,1,-2,1) e_3^T (+)
     C (e_3 - e_1) (x) (m o m), m = (1,0,w^2,0,w): level identity; single-row parts (3,0,1,0), single-column parts (0,0,0,1,0): NOT line-spanned;
     (dim T_1, rank q, bound) = (10, 4, 8). m is isotropic, so SP8 does not apply; the FO2 bound 8 excludes it.  (Found once; whether it moves in
     a family is not known.)
 14.7 Consequence for the structure route: the right class is not "line-spanned". All non-line pieces found are (i) skew two-column blocks
     {x e_a^T + a (Jx) e_b^T : x in V} and (ii) rank-one elements x (x) v with x, v both of support >= 2 -- in every example together with a
     3-dim single-row part e_0 (x) {1,m}^perp and its split element e_i m^T (u = 3). Conjecture (for the next round): every 6-dim deletable-row
     space is spanned by single-row, single-column, rank-one and skew-block elements; and u = 2, 1 spaces are line-spanned (only line-spanned
     ones were found, but the search there is thin). The neutral-column analogue (4x4 types (3,0), (4,1), (5,2)) was not started.
STATUS 22:06: structure route answered negatively for "line-spanned" (exact BLOCK family and RANK-ONE space), both still FO2 <= 8 [exact].
 Targets 2-4 of round 6 not started.
 14.8 THE DOUBLE-BLOCK FAMILY, EXACT (u = 2, S has NO line element): for every (a, b),
         M_D(a,b) = e_0 (x) {(al,be,g,g,g) : al+be+3g = 0} (+) {x e_0^T + a (Jx) e_1^T : x in V} (+) {e_2 w^T + b e_3 (J'w)^T : w in W'},
     W' = sum-zero vectors on the columns 2,3,4, J' its rotation: LEVEL for all (a,b) [exact: no level equations, gb/blockfam2.py]; at (1,1):
     single-row parts (2,0,0,0), single-column parts 0, (dim T_1, rank q, bound) = (10, 4, 8), Omega = span(e_0, e_1, 1_{234}) (reg2/dblock_exact.py).
     (S6-FO2) on the WHOLE family [exact]: dim T_1 <= 10 for every (a,b) (gen_rank dblock, 40 greedy 15x15 minors generate (1)) and rank q >= 3
     for every (a,b) (gb/pdblock_rank.py: unique lifts of rho = e_0, e_1, Gram minors = (1)); so FO2 bound <= 8. No SP8 needed.
 14.9 Bigger censuses [numerical]: u = 2: 19 hits / 1000 starts (16 line-spanned, 1 double-block, 2 with line rank 2/4), u = 1: 8 hits / 800
     (3 line-spanned, 5 with line rank 3/5 -- skew blocks on two rows); all FO2 <= 8.
 14.10 EMPIRICAL STRUCTURE LAW (BL) [numerical, reg2/bispan.py, bispan_all.py]: every 6-dim 4x5 level space found is spanned by its elements
     supported in AT MOST TWO ROWS or AT MOST TWO COLUMNS. Tested: all 63 deletable-row hits of dr35.py (47 line-spanned, 16 not) and all 84 other
     saved 6-dim spaces (rows' LM files and sparse limits, EC moves, M*, Type F kernels, linespan/ext/p21111 hits; 59 line-spanned, 25 not):
     147 / 147, 41 of them NOT line-spanned. (A generic 6-dim subspace of C^{4x5} meets no 2-row (10-dim) or 2-column (8-dim) coordinate
     subspace, so (BL) is a strong constraint.)  Line-spanned = the special case "at most ONE row or column".
     Suggested new structure statement: (BL) + a classification of the two-row and two-column pieces (2x5 and 4x2 level-type problems; the skew
     blocks {x e_a^T + a Jx e_b^T} and their transposes, the rank-one elements x (x) v, and lines) would reduce (S6-FO2) to a finite "bi-line
     pattern" table, to be treated with the gen_rank / lift tools as for the line-spanned patterns.
STATUS 22:10: (BL) holds on 147/147 six-dim spaces; double-block family certified FO2 <= 8 exactly. Writing the round-6 report.
 14.11 Second-generator check (target 4, partial; reg2/second_gen.py): (2,2|1,1)BB recomputed by a different method (kernel of the full FO
     matrix over Q(p), gcd of the principal 3x3 minors of q on a polynomial kernel basis): generic dim T_1 = 10, gcd = 5184 (p-1)^4 (p+1)^4, and at
     p = +-1 exactly (10, rank 4, 8). Independent of the lift/Gram certificate (gb/p2211_rank.py) for the rank part; the bound dim T_1 <= 10
     everywhere still rests on the gen_rank minors.
STATUS 22:11: round 6 report being sent; dr35 censuses u = 2, 1 still running (light jobs, logs reg2/gb/runs/dr35_u2c.log, dr35_u1c.log).
 [22:11 update of 14.10: with the later dr35 hits, 71 deletable-row hits (51 line-spanned, 20 not) + 84 others: 155 / 155 bi-line spanned.]

# ROUND 7 (reg2, start ~22:11 UTC). Targets: (1) (BL) -> finite table; (2) prove (BL) for deletable rows; (3) (1,1,1|1,1,1), hit-free patterns;
# (4) Omega/E_0 certificates of the (3,10,8) curves.
## 15. Bi-line pieces and SKEW DEFORMATIONS
 15.1 Piece census (reg2/pieces.py; all 6-dim spaces at hand): the non-line part of every space is carried by ONE row-pair or column-pair piece
     adding 2 dimensions (skew block type), or by rank-one elements x (x) v adding 1 (several in the noisy LM files without clean sparse limits).
     Signatures: ('row', dim 4, +2) x 12, ('col', 3, +2) x 10 [BLOCK], ('row', 1, +1, rank one) x 7, ('row', 3, +2) x 8, ('row', 2, +2) x 4,
     double-block x 2, ... Every 2-row / 2-column piece P is only constrained by P_1 and P_2 by itself (P_3 = P_4 = 0 on it), i.e. P is isotropic
     for beta((x,y),(x',y')) = (Sx)(Sy') + (Sx')(Sy) - <x,y'> - <x',y>: a continuous family -- the finiteness has to come from the coupling.
 15.2 MECHANISM (empirical, reg2/skewdef.py): the non-line spaces are SKEW DEFORMATIONS of special members of line-spanned families: a 2-dim
     single-column part V (x) e_a (V nondegenerate) is replaced by {x e_a^T + t (J_V x) e_b^T : x in V} (J_V = generator of so(V)), or a 2-dim
     single-row part e_i (x) W by {e_i w^T + t e_j (J_W w)^T}. P_2 on the deformed piece is t <x, J x> = 0 by skewness; whether P_3, P_4 survive
     depends on the member: BLOCK = deformation of (3,1|2) at m with m_a = m_b = 0; DOUBLE-BLOCK = double deformation of (2,2|2)-type members;
     generic members of (2,1,1|2)(ii)/(iii), (2,2|2), (3,1|2), (3|2,1), (3|3) admit NO level deformation; (2,1|3) admits the row deformation
     0 -> 1 for all u; (2,2|1,1)BB admits row deformations 0 -> 1, 2, 3 for all parameters.
 15.3 (2,2|1,1)BB ROW DEFORMATIONS, EXACT: B(p,t) = BB with row 0 replaced by {e_0 w + t e_j (Jw) : w in sum-zero(cols 0,1,2)}, j = 1, 2 (j = 3 ~ 2):
     level for all (p,t) [exact: no level equations]; numerically (10,4,8); EXACT: dim T_1 <= 10 (gen_rank BBdef1/BBdef2: 15x15 minors leave only
     t = 0 points (= BB, certified in 13.1) and (p,t) = (-1/2,1) resp. (1,1), both (10, rank 4, 8) exactly, reg2/bbdef_pts.py; x = (0,0,1,-1)
     sub-families: minors generate (1)); rank q >= 3 for every member (gb/p2211def_rank.py: d_1 is still in E_0, unique lifts of e_3, e_4, Gram
     minors = (1) in both x-charts). So FO2 bound <= 8 on both deformation families.
 15.4 SYSTEMATIC DEFORMATION TABLE (reg2/gb/defo_scan.py; exact level ideals of the deformed families, Singular minAssGTZ; log
     reg2/gb/runs/defo_scan.log). For every exact line-spanned family with a 2-element single-line group and every target line, the loci of
     the base parameters on which the skew deformation (parameter t) stays level:
       LEVEL FOR ALL (base, t): (2,2|1,1)BB row 0 -> 1,2,3 [15.3, closed]; (2,2|2) row 0 -> 1; (2,1,1|2)(iii) row 0 -> 2; (2,1|2,1)V0 col 4 -> 3;
                                (1,1,1|2,1)A1 col 4 -> 3; (2,1|3) row 0 -> 1 (all u, hand-built, gen_rank 213def running).
       SPECIAL LOCI: (2,2|2) col 0 -> 1 at mu = (0,1,1,1), col 0 -> 2 at mu = (0,1,0,0), row 0 -> 2,3 at 7 points, row 1 -> 0 on a conic;
                     (2,1,1|2)(iii) row 0 -> 1,3 at 7 points; (3,1|2) col 4 -> k on m_k = 0  [= the BLOCK family, 14.5, closed];
                     (3|2,1)a, (2,1|2,1)Vnii, (1,1,1|2,1)B1 col 4 -> 3 at p^2+p+1 = 0; (2,1|2,1)V0 col 4 -> 1, 2 at s = 0, -1;
                     (2,2|1,1)BD row 1 -> 0 on the isotropic conic of v; (2,1,1|2)(ii) col 0 -> k on the SIGMA curves, row 0 -> 1,2,3 on
                     isotropic loci (c = b isotropic and one more component).
       NONE: (2,1|2,1)Vni, (1,1,1|2,1)B2, (2,1,1|1,1)(a,a) and ACC, and all other (family, target) pairs listed in the log.
     This is the "finite bi-line table" at the level of single skew deformations (double deformations, e.g. DOUBLE-BLOCK, and the rank-one
     mechanism of 14.6 are not covered by this scan).
 15.5 Numerically every LEVEL-FOR-ALL deformation is (e, dim E_0, dim Omega, dim T_1, FO2) = (4 or 3, 7, 2, 9, 7) (reg2/gb/defo_inv.py);
     exact gen_rank certificates (reg2/gb/gen_rank_defo.py) running at the end of the round.
 15.6 TARGET 4 (independent certificate, (2,2|1,1)BB; reg2/gb/gen_bb_om.py): Omega-test (complement of span(e_3, e_4, 1_{012})) unit in all
     charts (both x-charts, both pivot charts), E_0-test unit in all 13 charts per pivot chart, calibrations non-unit: dim Omega <= 3 and dim E_0 <= 7
     for every member, i.e. dim T_1 <= 10 EVERYWHERE without the minors tool. With 14.11 (rank via the gcd method + exact p = +-1) and the exact
     x = (0,0,1,-1) point this is a complete second certificate of FO2 = 8 on BB.
 15.7 (BL) update: 103 deletable-row hits (26 not line-spanned) + 84 others = 187 / 187 bi-line spanned. Every deletable-row hit has FO2 <= 8.
STATUS 22:25: deformation table (15.4) and second BB certificate (15.6) done; gen_rank certificates of the deformed families running.
STATUS 22:31: round 7 report sent; two 3-parameter gen_rank runs (213def, 22_2 row 0->1) still running with 25-min timeouts.

# ROUND 8 (reg2, start ~22:32 UTC). Targets: (1) close the deformation table; (2) second scan + rank-one mechanism; (3) why skew; (4) (1,1,1|1,1,1).
## 16. Closing the deformation table
 16.1 NEW TOOL reg2/gb/omega_e0.py FAMILY DEFO OMEGA DDIR NPIV: Omega-test with X FREE (no pivots; valid everywhere) for the normalisation
     rho_c = 0, sum_{j != c} rho_j = 0; E_0-test with X normalised at 7 pivot coordinates chosen numerically from a spanning set of M + C d,
     each pivot set localised by z * Delta = 1 (Delta = the exact 7x7 pivot minor); the uncovered locus V(Delta_1, .., Delta_NPIV, relations)
     is printed and treated separately.  Seconds to a minute per family, < 0.5 GB.
 16.2 THE FIVE LEVEL-FOR-ALL DEFORMATIONS ARE CLOSED [EXACT, char 0]  (log reg2/gb/runs/omega_e0.log; d found numerically and then used exactly):
     (2,1,1|2)(iii) row 0 -> 2 (Omega = span(1,e_0), d = d_1): Omega-test unit (4 charts), E_0-test unit (4 pivot sets x 13 charts); uncovered:
         t = 0 (undeformed, section 9.6) and the line {m4^2 - 3m4 + 3 = 0, m3 + m4 = 3} x t: gen_rank_defo with these relations, 16x16 minors = (1).
     (2,1|2,1)V0 col 4 -> 3 (Omega = span(1,e_3), d = d^3): Omega/E_0 unit; uncovered s = -1 (any t): minors = (1).
     (1,1,1|2,1)A1 col 4 -> 3 (Omega = span(1,e_3), d = d^3): Omega/E_0 unit; uncovered only at t = 0 (undeformed A1, section 11.5).
     (2,1|3) row 0 -> 1 (family 213def, Omega = span(1,e_4), d = d^4): Omega/E_0 unit; uncovered: t = 0 (undeformed) and the line u = (3,-1,-1,-1)
         x t, where dim T_1 = 9 numerically; minors selected ON the line (family 213defu3) = (1).
       => dim T_1 <= 9 for every member of these four deformation families.
     (2,2|2) row 0 -> 1: E_0-test unit (4 pivot sets; uncovered line mu = (0,1,0,1) x t: minors (fixed mu) leave only t = 0, the undeformed 0/1
         member (10,4,8) of section 8.3); Omega-test NOT unit: elimination ideal (t(m3 - m4), m3^2 - m3, m4^2 - m4), i.e. for t != 0 dim Omega
         jumps exactly on the curves mu = (0,1,0,0) and mu = (0,1,1,1) (x t). On these curves: (10,4,8) numerically; EXACT dim T_1 <= 10
         (15x15 minors at fixed mu = (1)) and rank q >= 3 for every t (gcd of the principal 3x3 minors over Q(t) is a constant: 316224 resp.
         44623872; reg2/def22_curve.py). => FO2 <= 8 on the whole family.
     Together with 15.3 ((2,2|1,1)BB row deformations): ALL six level-for-all deformations satisfy FO2 <= 8 exactly.
 16.3 SPECIAL-LOCUS DEFORMATIONS (one-parameter families over the special base points; reg2/gb/certify_defo.py: exact sympy basis, level
     identity, generic dim T_1 over Q(t), gen_rank at the fixed base point with r = 25 - generic dim, gcd of 3x3 minors when dim T_1 = 10, exact
     leftover points; log reg2/gb/runs/certify_defo.log) -- results being collected (see 16.6).
 16.4 SECOND SCAN (reg2/gb/defo_scan2.py, log runs/defo_scan2.log): double deformations exist ONLY over the special points of (2,2|2):
     row 0 -> 1 followed by col 0 -> 1 at mu = (0,1,1,1), col 0 -> 2 at mu = (0,1,0,0), row 1 -> 0 on the conic 3m3^2 - 2m3m4 + 3m4^2 - 2m3 - 2m4 + 3 = 0;
     col 0 -> 1 (mu = (0,1,1,1)) or col 0 -> 2 (mu = (0,1,0,0)) followed by row 0 -> 1, 2, 3.  None for (2,2|1,1)BB, (2,1,1|2)(iii), (2,1|2,1)V0,
     (1,1,1|2,1)A1, (3,1|2)-BLOCK.  (DOUBLE-BLOCK, 14.8, is of this kind and is closed.)
 16.5 WHY SKEW (rigorous, target 3). LEMMA SK. Let M be a 4x5 level space and P = M cap {supported in the columns a, b} = {x e_a^T + y e_b^T}.
     For a matrix supported in two columns, P_3 = P_4 = 0, P_1 = Sx + Sy and P_2 = (Sx)(Sy) - <x,y> (only pairs (x_r, y_s), r != s).
     Hence on P: Sx + Sy = 0 and, polarised, <x,y'> + <x',y> = (Sx)(Sy') + (Sx')(Sy) = -2 (Sx)(Sx').  On the subspace P_0 = P cap {Sx = 0}
     (codim <= 1) this reads <x,y'> = -<x',y>: if P_0 has no line element, y = A x with A SKEW for <.,.> on X_0 = pi_a(P_0).  So skewness is not
     an extra assumption: it is P_2 for sum-zero column parts.  Consequences: (i) dim X_0 <= 3 (X_0 inside 1^perp of C^4); a skew A on a 3-dim X_0
     has a kernel line (odd dimension), which is a single-column element -- so a column block contributes at most 2 dimensions beyond the line
     span, as observed in every example (15.1); (ii) on a 2-dim nondegenerate X_0, A = t J_X0 + (a map into X_0^perp), exactly the deformation shape.
     The same holds for two-row pieces (row vectors in C^5; X_0 inside 1^perp of C^5 is 4-dim, so a 4-dim skew row block is not excluded by P_2
     alone).  RANK-ONE: P_2(x v^T) = (1/2)((Sx)^2 - <x,x>)((Sv)^2 - <v,v>) and P_1 = (Sx)(Sv), so a rank-one element with Sx = Sv = 0 needs x or v
     isotropic -- the RANK-ONE space has v = m o m isotropic.  What is NOT proved: that a 6-dim level space has no other non-line piece (e.g. a
     non-skew block with Sx != 0, or a 4-dim row block); (BL) itself.
 16.6 SPECIAL-LOCUS DEFORMATIONS, results [EXACT] (certify_defo.py / gen_rank_defo.py with fixed base points, logs runs/certify_defo*.log):
     rational base points -- all FO2 <= 8:
       (2,2|2) col 0 -> 1 at mu = (0,1,1,1) and col 0 -> 2 at mu = (0,1,0,0): generic dim T_1 = 10; 15x15 minors = (1); gcd of 3x3 minors c t^4;
           t = 0 exact (10,4,8).
       (2,2|2) row 0 -> 2 and row 0 -> 3 at the 7 points (m3,m4) in {(0,-1),(1,2),(1,1),(2,1),(-1,0),(0,0),(1/2,1/2)}: dim T_1 = 9 generically
           (minors = (1) or leave t = 0 only, exact (9,3,7)/(10,4,8)) except (1,1), (0,0): dim T_1 = 10 generically, minors = (1) or t = 0,
           gcd constant or c t^4, t = 0 exact (10,4,8).
       (2,1,1|2)(iii) row 0 -> 1 and row 0 -> 3 at the same 7 points: dim T_1 <= 9 (minors = (1)).
       (2,1|2,1)V0 col 4 -> 1 at s = 0 and col 4 -> 2 at s = -1: dim T_1 <= 9.
     omega base points (p^2 + p + 1 = 0; minors selected at omega): (3|2,1)a, (1,1,1|2,1)B1 col 4 -> 3: leftovers only at t = 0 (undeformed,
       certified in round 4); (2,1|2,1)Vnii col 4 -> 3: leftover lines s = 0, -1 (x t) closed by minors at fixed s: dim T_1 <= 9.
     conics (minors selected at numerical points ON the conic, new in gen_rank.py): (2,2|2) row 1 -> 0 and (2,2|1,1)BD row 1 -> 0: leftovers
       only at t = 0 (undeformed members, certified in rounds 2 and 5).
     (3,1|2) col 4 -> k on m_k = 0 = the BLOCK family, closed in 14.5.
     STILL OPEN: (2,1,1|2)(ii): col 0 -> k on the SIGMA curves (generic (10,4,8); dim T_1 <= 10 by minors except isotropic points; rank q >= 3 not
       yet certified) and row 0 -> j on its isotropic / degree-high loci (part of these loci has a = cross4(b,c) = 0, i.e. lies outside the
       6-dim family, and must be redone in the (d) parametrisation); the double deformations of 16.4 (over the (2,2|2) special points); the
       rank-one mechanism scan.
STATUS 22:47: deformation table: all level-for-all and all point/conic special-locus deformations closed exactly; open: (2,1,1|2)(ii) loci and
 double deformations. Writing the report.

# ROUND 9 (reg2, start ~22:47 UTC). Targets: (1) (2,1,1|2)(ii) deformations; (2) double deformations; (3) extend Lemma SK; (4) (1,1,1|1,1,1).
## 17. (2,1,1|2)(ii) deformations, double deformations, SK
 17.1 NEW TOOL reg2/gb/lift_gram.py FAMILY DEFO FIX RHO1 RHO2 DDIR NPIV: generic lift/Gram certificate (unknown lifts of rho = e_RHO1, e_RHO2,
     X normalised at numerically chosen pivots of M + C d, each localised by z*Delta = 1; Gram of q_Y on span(d, tau, t_1, t_2) for two Y; ideal of
     its 3x3 minors + "lifts exist" elimination ideal; uniqueness of the lifts checked). certify_defo.py now accepts extra exact points.
 17.2 SIGMA-CURVE COLUMN DEFORMATIONS of (2,1,1|2)(ii) [EXACT]. Chart (b_1 = c_1 = 1): col 0 -> 2 on SIGMA_2 = {b_2 = c_2 = 0, <b,c> = 0}
     (generically (10,4,8), Omega = span(e_0, e_2, 1_{134}), d = d_0): rank q >= 3 on three pivot charts (lift_gram), whose union covers the
     family except (b3,c3,t) = (1,-1,1/3) [exact: (10, rank 4, 8), certify_defo extra point] and the points b = c isotropic (there a = cross4(b,c)
     = 0: not 6-dim members); dim T_1 <= 10 by 15x15 minors (round 8) except t = 0 (the undeformed SIGMA members, (10,4,8) by section 9.4) and
     the same degenerate points.  col 0 -> 3, 4 on SIGMA_3, SIGMA_4: column symmetry (2,3,4).  Chart (b_1 = 1, c_2 = 1) (family 211ii_c2): the
     scan gives col 0 -> 3, 4 on SIGMA_3, SIGMA_4 only; lift_gram on SIGMA_3: rank >= 3 on 3 charts covering everything except t = 0 and the
     degenerate points c ~ b; minors: dim T_1 <= 10 except the same.  => FO2 <= 8 on all SIGMA-curve deformations.
 17.3 THE (d) COMPONENT (c = b isotropic, a = cross4(b, b o b); family 211d) [EXACT]: scan: col 0 -> k at the 3-column isotropic b (b ~ (1,w,w^2)
     with a zero; 1-parameter families over Q(omega)): generically (10,4,8); 15x15 minors (omega) leave only t = 0 (undeformed, section 9.4);
     lift_gram (two charts, Delta_1 = 4(3t-1)(b3+1)(b3+2), Delta_0 = 4t(...) with value 6+6w at b3 = w at t = 1/3): rank q >= 3 for all t != 0.
     row 0 -> 1, 2 at b ~ (1,-1,i,-i) (one orbit under the column symmetry): (9,3,7); 16x16 minors (on-locus) leave only t = 0. => closed.
 17.4 (ii-g) ROW DEFORMATIONS: the scan loci on chart 1 are (a) b = c isotropic (degenerate, not 6-dim) and (b) curves with b or c isotropic
     (e.g. through b = (1,1,-1-i sqrt2,-1+i sqrt2), c = (1,-1,0,0)); numerically (9,3,7) there; exact certificate RUNNING (4-parameter ideal,
     1.3 GB) -- see the final report.
 17.5 TARGET 3, extending SK.
   (a) LEMMA SK2 [rigorous]. Let P = {e_r w^T + e_j (Bw)^T : w in W} be a two-row piece of a level space M with W inside 1^perp and B skew on W
       (as forced by SK). For Z in M put zeta := sum_{k != r, j} Z_k (row vector). The mixed coefficient of P_3 on (Y_w, Y_w', Z) uses the row-r and
       row-j entries of Y_w, Y_w' and a row-k entry of Z, so it equals e(w, Bw', zeta) + e(w', Bw, zeta) = -(S zeta)(<w,Bw'> + <w',Bw>) +
       2 (T(w, Bw', zeta) + T(w', Bw, zeta)).  Hence: the bilinear form (w, w') -> <w o zeta, B w'> is SKEW on W for every Z in M.  For W = 1^perp
       (a 4-dim row block) this is a linear condition "B commutes with diag(zeta) modulo 1" for every zeta in the span of the partial row sums of M;
       a skew map commuting with a diagonal map with enough distinct values has rank <= 2.  (Proof of the rank bound in general: not done.)
   (b) [numerical, reg2/freerow_def.py] SKEW DEFORMATIONS OF A FULL FREE ROW: for the Type F spaces M_L080_col0, M_ex2_row4 (free row (+) 2-dim
       N) and every target row, random skew B are never level, but Gauss-Newton over B in so(4) finds level solutions at EVERY start (20/20);
       in all of them rank B = 2 (singular values (1,1,0,0)), i.e. the deformed space is "2-dim single-row part + 2-dim skew row block" -- the
       standard 2-dim mechanism, never a genuine 4-dim block; their invariants are (9,3,7) resp. (10,4,8) (FO2 <= 8; the Type F value 9 is lost).
   (c) NON-SKEW two-column elements (sum x != 0): a first test found extensions S5 + C E, but E = e_3 (e_0 - e_2)^T is a single-row element (a line);
       the corrected test (rank [x y] = 2 enforced, reg2/nonskew_ext.py, calibrated on a BLOCK space) is running (17.7).
   (c') corrected non-skew test (reg2/nonskew_ext.py with rank [x y] = 2 and E outside the line span; calibration on the BLOCK space re-finds
       its skew block, 3/60 cases): every non-skew hit so far is DECOMPOSABLE -- E = (single-row element e_i (e_a - e_b), which has sum x != 0) +
       (an element of a skew block); e.g. dr35_u2_s52_870: the extension S5 + C E is the original space. No genuine non-skew block found
       (evidence only; the filter "no line element of the piece has sum x != 0" is the right criterion and is not yet automated).
 17.6 DOUBLE DEFORMATIONS over the (2,2|2) special points [EXACT, partial]: (row 0 -> 1 or 2) + (col 0 -> 1) at mu = (0,1,1,1) and
     (row 0 -> 1 or 2) + (col 0 -> 2) at mu = (0,1,0,0) (two parameters t, t2): 16x16 minors all vanish (generic dim T_1 >= 10); 15x15 minors
     leave only t2 = 0 (the single row deformations on the special curves, closed in 16.2) and (t,t2) = (0,0): dim T_1 <= 10 EVERYWHERE.
     rank q >= 3 on these two-parameter families: NOT yet certified (lift_gram.py handles one deformation; needs the double version).
     The conic double deformation (row 0 -> 1 + row 1 -> 0 on 3m3^2-2m3m4+3m4^2-2m3-2m4+3 = 0): not done.
 17.7 (2,1,1|2)(ii) row deformations on the isotropic curves (17.4): the 4-parameter minor run (1.3 GB) was stopped after 15 min; numerically
     (9,3,7); exact certificate open (should use a parametrisation of the curve: b on the isotropic conic, c determined).
STATUS 23:04: round 9 report: SIGMA and (d) deformations of (2,1,1|2)(ii) closed; double deformations dim T_1 <= 10; SK2 + free-row rank-2
 phenomenon; open: (ii) row curves, rank of double deformations, conic double deformation, non-skew exclusion.

# ROUND 10 (reg2, start 23:05 UTC). Targets: (1) rank q of the (2,2|2) double deformations + conic; (2) (ii-g) row curves; (3) SK2 -> rank B <= 2,
#   automated non-skew filter; (4) (1,1,1|1,1,1).  EVIDENCE: every exact verdict of rounds 3-9 re-run with saved output, reg2/evidence/ (18.0).
## 18. Round 10
 18.0 EVIDENCE RE-RUN (verify2 note): reg2/evidence/rerun_cheap.sh re-runs 102 cheap exact certificates of rounds 3-9 (gen_rank, gen_rank_defo,
     omega_e0, lift_gram, certify_defo, the point/exact scripts dr211_special, p312_special, p33_cert, el_exact, nc_cert, p2211_*, p21111_*,
     block*, dblock*, rankone_exact, second_gen, p2211def_rank, gen_bb_om, def22_curve, ...) with output in reg2/evidence/logs/<round>_<name>.log,
     index reg2/evidence/logs/_index.txt: 102/102 exit 0, verdicts identical to the ones recorded in rounds 3-9.  (blockfam.py / blockfam2.py print
     "level equations: 0" = level for every parameter; the Singular error after it in r6_blockfam.log is the empty-ideal call, harmless.)
STATUS 23:21: evidence re-run done (102/102); double-deformation lift_gram written (lift_gram.py defo2=...), point cases certified; conic and
 (ii-g) curve (new polynomial parametrisation over Q(w)) minors running.
 18.1 DOUBLE DEFORMATIONS over the (2,2|2) special points: rank q >= 3 [EXACT] -- all six point families closed.
     Tool: reg2/gb/lift_gram.py now takes defo2=kind,idx,tgt (second skew deformation with parameter t2; both J-maps are computed on the
     undeformed basis -- the two 2-element groups are disjoint and the first deformation does not touch the second group, so this equals the
     sequential construction used by the scan and by reg2/gb/num_double.py).  Numerics (reg2/gb/num_double.py): all six families (10,4,8),
     Omega = <e_0, e_1, e_2+e_3+e_4> (mu = (0,1,1,1)) resp. <e_0, e_2, e_1+e_3+e_4> (mu = (0,1,0,0)), d = d_1 (row 1 deletable).
     lift_gram (logs reg2/evidence/logs/r10_lift_double_<fam>_row,0,<k>.log): lifts exist and are unique on each chart Delta != 0, and the
     rank<=2 ideal (3x3 minors of both Gram matrices) is UNIT on every chart:
       22_2_11 (mu=(0,1,1,1)) row 0->1 + col 0->1: Delta in {-45t^2, -15t(3t2+1), 15t}      -> rank q >= 3 for t != 0
       22_2_11               row 0->2 + col 0->1: Delta in {5(3t-1), -150 t t2, 5t}       -> t != 0
       22_2_11               row 0->3 + col 0->1: Delta in {-5, 150 t2, -150 t}            -> EVERYWHERE (chart 0 has constant pivot)
       22_2_00 (mu=(0,1,0,0)) row 0->1 + col 0->2: Delta in {45t t2(t+5), -15t, 15t}       -> t != 0
       22_2_00               row 0->2 + col 0->2: Delta in {-150 t t2, -75t, -5t}         -> t != 0
       22_2_00               row 0->3 + col 0->2: Delta in {-150 t t2, -75t, -10t}        -> t != 0
     (the first row 0->3 attempt used the normalisation rho = (0,3), for which the lift locus is EMPTY ("LIFTS EXIST where: 1"); rerun with the
     Omega normalisation of the numerics -- both logs kept, the rerun log carries a comment line.)
     dim T_1 <= 10: 15x15 minors (r9_double_*.log, r10_double_22_2_*_0_3.log) leave only t2 = 0 (resp. (t,t2) = (0,0)).
     Leftovers: t = 0 is the single column deformation col 0 -> 1 (mu=(0,1,1,1)) / col 0 -> 2 (mu=(0,1,0,0)), closed in 16.6 (generic (10,4,8),
     gcd of 3x3 minors c t^4, t = 0 exact (10,4,8)); t2 = 0 is the single row deformation row 0 -> k on the special curves / at the special points,
     closed in 16.2/16.6.  => FO2 <= 8 on all six double-deformation families.  (Row 0 -> 3 after the column deformation was listed by the scan
     (16.4) but missing from 17.6; added here.)
 18.2 TARGET 3 -- LEMMA SK3 (rank bound for a 4-dim row block) [rigorous for (i)-(iii); (iv) = remaining case, exact check in 18.4].
     Setting: M a level 4x5 space containing P = {X_w = e_r w^T + e_j (Bw)^T : w in W}, W = 1^perp (C^5) (a FULL 4-dim row block), r != j;
     k, l = the other two rows.  Write <.,.> for the bilinear dot product, pi = projection C^5 -> 1^perp along 1.
     (i)  P_1(X_w) = S(Bw) = 0, so B maps W into W; P_2(X_w) = -<w,Bw> (sum-zero rows), so B is skew.  Hence B = K|W for a UNIQUE 5x5
          skew-symmetric matrix K with K 1 = 0 (extend by K 1 = 0; skew on W and K 1 = 0 <=> K^T = -K).
     (ii) (SK2 sharpened) For Z in M let zeta_Z = Z_k + Z_l.  The (2,1)-part of P_3 on (X_w, X_w, Z) is
          E(Bw, w, zeta) = -(S zeta)<Bw,w> + 2 T(Bw, w, zeta) = 2 w^T diag(zeta) K w   (S w = S Bw = 0),
          so Pi (DK - KD) Pi = 0 on W x W, D = diag(zeta).  DK - KD is SYMMETRIC with zero diagonal; a symmetric matrix vanishing on W x W
          is u 1^T + 1 u^T, whose diagonal is 2u; hence u = 0 and   [diag(zeta_Z), K] = 0,  i.e.  K_ab = 0 whenever zeta_a != zeta_b.
     (iii) If some zeta_Z is NOT constant: K is block diagonal along the level sets S_1..S_m (m >= 2) of zeta_Z, each block K_S skew with
          K_S 1_S = 0 (rows of K sum to 0 and K is block diagonal), so rank K_S <= 2 floor((|S|-1)/2); over all partitions of 5 into >= 2 parts
          the total is <= 2 ((4,1),(3,2),(3,1,1): 2; the others 0).  So rank B <= 2, B has a >= 2-dim kernel, and P contains a >= 2-dim
          single-row part {e_r w : w in ker B}: the block is the standard "2-dim single-row part + 2-dim skew deformation" (or less).
     (iv) Remaining case: zeta_Z constant (= lam_Z 1) for EVERY Z in M.  Normalise z_r in C 1 (subtract X_{pi z_r}).  The (1,1)-part of P_2 on
          (X_w, Z) is -( <w, z_j + zeta> + <Kw, zeta> ) (z_r constant drops out), so pi(z_j + zeta) = K zeta = 0, i.e. z_j constant too.  Hence
          every Z is congruent mod P to  a e_r 1 + b e_j 1 + e_k p + e_l (lam 1 - p),  lam = -a-b (P_1).  These spaces are tested EXACTLY in 18.4
          (Singular over Q, all level equations + Rabinowitsch y*Pf(K) - 1, 4 echelon charts for <Z1,Z2>).  Numerically (reg2/sk3_search.py,
          Gauss-Newton with Pf(K) = 1, 12 starts): no solution, residual stalls at ~1.
     Check against the numerics of 17.5(b): the free-row deformation solutions have zeta = multiples of e_4 (non-constant), and their K has
     zero row/column 4 and rank 2 -- exactly case (iii).
     Scope: (i)-(iii) need W = 1^perp.  For a 3-dim W the skew FORM b(w,w') = <w,Bw'> is degenerate (odd dimension) but the MAP B can have rank 3
     (B w_0 in W^perp cap 1^perp); not treated.
 18.3 TOOL FIXES (round 10, reg2/gb/gen_rank.py; backups *.bak_r10): (a) greedy_num normalises rows before the numerical rank tests and
     (b) FO entries are reduced EXACTLY modulo an omega relation nm^2+nm+1 (w^2 -> -1-w) before minor selection and before writing A.  Without
     them the high-degree families of 18.5 got 0 resp. 5 of 30 minors (catastrophic cancellation at w = exp(2 pi i/3)).  Effect on earlier runs:
     none on validity (a selected minor is a genuine minor; fewer minors can only enlarge the leftover set); the round-8/9 omega runs ended
     UNIT / with certified leftovers anyway.  gen_rank_defo.py: fix=name:value now also accepts values alpha + beta*w in Q(w).
STATUS 23:36: double deformations at the 6 special-point families closed (18.1); Lemma SK3 written (18.2), exact check of its remaining case
 next; (ii-g) curve rerun with fixed minor selection and the parametrised conic double deformation running.
 18.5 (ii-g) ROW-DEFORMATION CURVES of (2,1,1|2)(ii) [EXACT, in progress -- see RESULT block for the final state].
     Homogeneous form: b, c are projective sum-zero vectors (scaling a basis element does not change M), so the family 211ii is
     M(b,c) = <(4,-1,-1,-1,-1)e_0, (0,a)e_0, (0,b)e_1, (0,c)e_2, col-0 elements>, a = cross4(1,b,c).  rel01 (/tmp/rel01.txt, from the scan,
     row 0 -> 1) is {<b,b> = 0, <b,c> = 0, + further equations}; rel02 (row 0 -> 2) is the same with b <-> c, i.e. the image of rel01 under the
     row swap 1 <-> 2 (which maps M(b,c) to M(c,b) and the row 0->1 deformation to row 0->2) -- so rel02 needs no separate certificate.
     Parametrisation (reg2/g2/param_g.py, g1_solve.sing, g1_ch.sing): b = x(s) = Q(q)p - 2<p,q>q, p = (1,w,w^2,0), q = (1,s,0,-1-s) (isotropic,
     sum zero, degree 2), and on rel01 c is RATIONAL in s: lex GB c3*h(s) - g(s), c2*... ; homogeneous c = c_h(s) (degree 6, gcd 1, <x,c_h> = 0
     checked).  Family 211g1 (gen_rank.py, params s, w, rel w^2+w+1); level equations of the row 0->1 deformation reduce to 0 modulo w^2+w+1
     [exact, r10_g1_levelcheck.log]; numerically (9,3,7) (defo_inv), Omega = <e_0, 1>, d = d_0.
     16x16 minors (5 genuine minors, r10_g1_row01_minors.log): leftover = 16 lines s = s0 (x all t):
       s0 in {-w-1, w, -1, 0, w+1, w-1, (w-1)/3}: fixed-s runs (r10_g1_left_1..7.log): UNIT for 5 of them, t = 0 only for s0 = w+1, w-1
         (t = 0 = undeformed (ii) member, closed by DR211-ii, round 3);
       3 quadratics s^2+w, s^2-2sw-w, s^2+2s-w: b || c (exact, r10_g1_degen.log), a = 0, dim M = 5 -- not 6-dim spaces;
       6 quadratics (3s^2-2sw+2s-3w, s^2-2sw+2s-w, 3s^2-2sw+2s+w+2, 3s^2-2sw+2s-w-2, s^2+2sw+2s+w+2, s^2-2sw-2s-w-2): runs with the
         quadratic as extra relation and on-locus minor selection (r10_g1_quad_1..6.log).
 18.4 LEMMA SK3, case (iv) is EMPTY [EXACT] => rank B <= 2 for every full 4-dim row block of a 6-dim level space.
     reg2/sk3_exact.py (rows r = 3, j = 0, k = 1, l = 2): M = P (+) <Z1,Z2> with Z of shape (iv), <Z1,Z2> in reduced echelon form w.r.t.
     (a, b, p_0..p_4) -- pivot pairs (a,b) [chart A], (a,p_0) [B], (b,p_0) [C], (p_0,p_1) [D] (first p-pivot moved to column 0, resp. the two
     p-pivots to columns 0,1, by S_5, which preserves the shape: K -> P K P^T); ideal = all level equations + y*Pf(K) - 1.
     Result (Singular over Q, logs reg2/evidence/logs/r10_sk3_{A,B,C,D}.log): std basis = (1) in all four charts (1-2 s each).
     CALIBRATION/validation: (1) with the rank condition replaced by y - 1 or y*k01 - 1 (r10_sk3cal_*.log) the ideal is STILL (1): shape (iv) admits
     no 6-dim level space for ANY K (including K = 0, a genuine free row); (2) the generated level polynomial agrees with an independent numpy
     evaluation F(J'+Y) - 120 at a random integer point (reg2/sk3_validate.py: 8192 = 8192); (3) Gauss-Newton (reg2/sk3_search.py) finds no
     solution of shape (iv) with Pf(K) = 1 (12 starts, residual stalls at ~1).
     => LEMMA SK3 [rigorous (i)-(iii) + exact (iv)]: if a 6-dim level 4x5 space M contains P = {e_r w + e_j Bw : w in 1^perp}, then rank B <= 2,
     so P contains a >= 2-dim single-row part of row r; i.e. a full free row can only be deformed by the standard 2-dim skew mechanism.  This
     proves the numerical observation 17.5(b) ("free-row skew deformations always have rank B = 2") and removes "genuine 4-dim row blocks"
     from the list of possible new mechanisms.  (3-dim row blocks: not covered, see 18.2 scope.)
     RESULTS: the six quadratic runs end UNIT (2) or with t = 0 only (4); the s = infinity point (b = (1,0,w^2,w), c = (1,-3,1,1), family 211g1inf,
     r10_g1_inf.log) leaves only t = 0.  So on the whole rel01 curve (6-dim members): dim T_1 <= 9 for t != 0  [EXACT]; t = 0 = undeformed (ii)
     members (DR211-ii).  rel02 / row 0 -> 2 by the row swap 1 <-> 2; row 0 -> 3 only on the degenerate b || c locus (scan).
     OTHER CHART: defo_scan.py 211ii_c2 (c = (c1,1,c3,.), r10_defo_scan_211ii_c2.log): the row 0 -> 1/2/3 loci are b || c (degenerate), the
     sextic curve and the c-isotropic curve, each with c1 generic (no component inside c1 = 0), hence closures of the chart-1 components --
     already covered by the homogeneous parametrisation.  => ALL (ii-g) ROW DEFORMATIONS OF (2,1,1|2)(ii): FO2 <= 8 (dim T_1 <= 9).  [EXACT]
     Note: b_0 = 1 is the standing normalisation of the (ii) family (column symmetry); the parametrisation also contains b_0 = 0 points (harmless).
 18.6 CONIC DOUBLE DEFORMATION (row 0->1 + row 1->0 of (2,2|2) on 3m3^2-2m3m4+3m4^2-2m3-2m4+3 = 0): OPEN (compute-limited).
     Numerics (num_double.py): (9,3,7), Omega = <e_0, 1>, d = d_1.  New: rational parametrisation over Q(w) (reg2/g2/conic_param.py, family
     22conic: m = ((1-w)/3, -w) + lam (1,s); D = 9s^2-6s+9; misses one conic point), level equations of the double deformation reduce to 0 mod
     w^2+w+1 [exact, r10_conic_levelcheck.log].  Runs: (a) 4-variable minors (m3,m4,t,t2 + conic) stopped after 22 min (r10_double_conic.log;
     an earlier seed-2 attempt was discarded: a concurrent evidence re-run overwrote its /tmp file); (b) parametrised minors (s,w,t,t2) timed out
     at 25 min (r10_conic_param_minors.log); (c) omega_e0.py (now with defo2= and FAMS relations) ran out of memory at the 1 GB cap
     (r10_conic_omega_e0.log).  Queued: REG2-CONIC-DD in QUEUE.md (omega_e0, 4 GB, <= 1 h; fallback minors, 2 GB, <= 2 h).
 18.7 NON-SKEW FILTER automated (reg2/nonskew_ext.py, nonskew mode only): a non-skew hit E (S x = 1) is discarded when the extended space has a
     single-row element e_i(alpha e_a + beta e_b) with alpha != 0 in the same column pair (then E - c*line is a sum-zero, i.e. skew-type, element).
     Run (r10_nonskew_filtered.log): 840 (space, hyperplane, column pair) cases, 12 hits, ALL 12 decomposable, 0 genuine non-skew blocks.
     Calibration (r10_nonskew_cal_filtered.log): skew mode on the BLOCK space dr35_u3_s1_3 still finds its skew block (3/60 cases).  (A first
     version applied the filter in skew mode too and removed the calibration hits -- fixed: the filter belongs to nonskew mode only.)  [numerical]
 18.8 (1,1,1|1,1,1): not started this round.
STATUS 00:07: round 10 report: double deformations at special points closed, (ii-g) row curves closed, Lemma SK3 (rank B <= 2) proved, non-skew filter automated; conic double deformation queued; (1,1,1|1,1,1) not started.
STATUS 00:07: round 11 started (targets: SK3 for 3-dim row blocks; finite mechanism list; (1,1,1|1,1,1); conic verdict). Conic fallback running in the pool (r10_conic_param_minors_big.log).

# ROUND 11 (reg2, start 00:06 UTC). Targets: (1) SK3 for 3-dim row blocks; (2) finite mechanism list; (3) (1,1,1|1,1,1); (4) conic verdict.
## 19. Round 11
 19.1 THE CONIC DOUBLE DEFORMATION IS TRIVIAL [EXACT] (target 4; reg2/g2/conic_trivial.py, log reg2/evidence/logs/r11_conic_trivial.log).
     For the (2,2|2) member (f22): det G(V0) = Q, det G(U) = 125 Q with Q = 3m3^2-2m3m4+3m4^2-2m3-2m4+3 (sympy factor), <V0,U> = 0
     identically, and on Q = 0 all 3x3 minors of [u0,u1,J_V v_k] and [v0,v1,J_U u_k] are divisible by Q.  Reason: on the conic both planes are
     degenerate, adj(G) has image ker G, so J_V(V0) = rad(V0) = V0 cap (C1 + U) cap 1^perp = V0 cap U, and likewise J_U(U) = U cap V0.
     Hence the deformation row 0 -> 1 adds t e_1 (J_V v) with J_V v in U -- an element of M -- and row 1 -> 0 adds t2 e_0 (J_U u) with J_U u in
     V0; so M(t, t2) = M(0, 0) for ALL t, t2: the family is the undeformed (2,2|2) member, closed by THEOREM DR22 (8.3).  The same argument
     shows the single deformation "row 1 -> 0 on the conic" of 16.6 is trivial.  Numerical confirmation (reg2/rowblock_probe.py on the doubly
     deformed space): rows (0,1) piece = 2 + 2 single-row elements, both Gram determinants ~1e-14.  => FO2 <= 8; REG2-CONIC-DD cancelled.
     (Lesson: a "deformation locus" from the scan can be a locus where the deformation is trivial -- check rank of J / membership first.)
 19.2 TARGET 1: 3-DIM ROW BLOCKS (partial).  Setting: P_0 = {e_r w + e_j Bw : w in W}, W = X_0 inside 1^perp, dim W = 3, B: W -> 1^perp
     (P_1), b(w,w') = <w,Bw'> skew (P_2); n spans W^perp cap 1^perp (W^perp = <1, n>).
     (a) [rigorous] REDUCTION.  b is a skew form on a 3-dim space, so it has a kernel vector w0: <w, Bw0> = 0 for all w in W, i.e.
         B w0 in W^perp cap 1^perp = C n, B w0 = mu n.  If b = 0 then B(W) inside C n, rank B <= 1.  Otherwise rank b = 2 and
         rank B = 3  <=>  mu != 0.  Then P_0 = (2-dim skew block on a complement V of w0, b|V nondegenerate)  (+)  the element
         e_r w0 + mu e_j n  (an R1-type element: w0, n in 1^perp, <w0,n> = 0, n perp V, and <w0, Bv> = 0 for v in V).  So a rank-3 block
         is "R2 + R1 on the same row pair", not a new kind of piece.  If W is nondegenerate (n.n != 0): B w = K w + beta(w) n with
         K in so(5), K 1 = K n = 0 (K|W = b-dual, kernel w0), rank 3 <=> beta(w0) != 0.
     (b) [numerical linear algebra, reg2/rb3_linear.py, rb3_incid.py] SK2 with a NON-constant zeta_Z: for the six level-set types of zeta
         and n with every zero pattern (random members), a rank-3 B satisfying skew + SK2(zeta) exists ONLY for
           (I)  zeta in <1, e_c> with n_c = 0  (then B(W) inside 1^perp cap e_c^perp, and the pairing W x (1^perp cap e_c^perp) is degenerate
                exactly along n -- proof: zeta = e_c in L_B <=> (Bw)_c = 0 on W; B is determined by b through the pairing unless n_c = 0);
           (II) zeta in <1, 1_S> with |S| = 2 and n supported on S (n ~ e_d - e_d', S = {d,d'}).
         All other types ((3,1,1), (2,2,1), (2,1,1,1), distinct values; generic W) force rank B <= 2 (B-space of rank <= 2 or zero).
         [the type list is numerical (random members of each zero pattern); special n inside a pattern not excluded.]
     (c) So rank B = 3 needs one of: (alpha) every zeta_Z constant, (I), (II) -- each a much smaller system (n fixed up to S_5 in (II),
         z_k + z_l restricted in all three).  Exact checks of (alpha), (I), (II): NOT done this round (the unreduced system has ~50 unknowns).
     (d) [numerical, robust census reg2/rowblock_census.py, log r11_rowblock_census.log] 187 spaces, all ordered row pairs: dim X_0 = 3 occurs
         187 times with rank B = 0 (168), 1 (3), 2 (16) -- NEVER 3; dim X_0 = 4 only for free rows (rank 0).  (A first, non-robust version
         reported rank 3 for ext_3/ext_4 rows (2,3): artefact -- their row-3 single-row element has |sum| ~ 5e-8 in the stored data, the
         sum-zero split misplaced it; the robust version splits off line elements before imposing S x = 0.)
     (e) numerical searches (rb3_search.py: rank-3 vs calibration; rb3_local.py: deformation of census spaces towards mu != 0) were
         INCONCLUSIVE (the calibration search found nothing either; the local solver did not converge) -- recorded, no claim.
 19.3 TARGET 2: FINITE MECHANISM LIST -- the precise statement for PROOF-MAP leaf 11.
   NOTATION. M = 6-dim level 4x5 space.  R_r, C_c = single-row / single-column parts; Lin(M) = sum of all of them, e := dim Lin(M).
   Pieces: P_rj = M cap {rows r, j}, Q_ab = M cap {columns a, b}; Pi(M) := sum of all 16 pieces.  Genuine part of a piece:
   G = P / (P cap Lin(M)), g = dim G.  (BL) is the statement Pi(M) = M.
   PROVED LOCAL STRUCTURE (every piece of every 6-dim level M):
   (S1) [SK, rigorous] P_0 = P cap {S x = 0} (x = first row/column part) has codim <= 1 in P and contains both line parts; on P_0, x -> y is
        a linear map B: X_0 -> 1^perp / Lambda (Lambda = y-parts of the second line part) with <x,Bx'> = -<x',Bx>; Lambda perp X_0;
        ker B = first line part.  A non-sum-zero element (P != P_0) has <x,y> = -(S x)^2.
   (S2) [SK2, rigorous] <x o zeta_Z, B x'> is skew on X_0 for every Z in M (zeta_Z = sum of the two other rows/columns of Z).
   (S3) ranks: columns: dim X_0 <= 3 and rank B <= 2 [SK].  Rows: dim X_0 <= 4; dim X_0 = 4 => rank B <= 2 [SK3, rigorous + exact, 18.4];
        dim X_0 = 3 => rank B <= 3, rank 3 = "R2 + R1 on the same pair" [19.2(a)], OPEN, never observed; dim X_0 <= 2 => rank <= 2.
   (S4) shape: a nondegenerate 2-dim skew part is B = t J_X0 + phi, phi: X_0 -> X_0^perp cap 1^perp (mod Lambda) [16.5(ii)].
   (S5) Lemma C / Theorem B bound PROJECTIONS (dim pi_rr'(L) <= 2n-3, 2x2-block projections <= 2); for a 6-dim M the row-pair bound
        dim pi_rr'(M) <= 7 is vacuous, so they force no piece to be non-zero.  They do not enter the decomposition below.
   THEOREM (mechanism decomposition, CONDITIONAL on (BL)).  If Pi(M) = M then  M = Lin(M) + sum over the 16 pieces of G_pi,  where every
   genuine part is of one of the types
        R1 / C1 : one sum-zero element e_r x + e_j y (x, y in 1^perp, <x,y> = 0) not in Lin(M)        [g = 1, rank 1]
        R2 / C2 : a 2-dim skew block {e_r x + e_j (tJx + phi x)}, X 2-dim                          [g = 2, rank 2]
        N       : at most one non-sum-zero element per piece, <x,y> = -(S x)^2, not explained by Lin  [adds 1]
        R3      : only if rank-3 3-dim row blocks exist (OPEN; = R2 + R1 on one pair)
   (no R4 by SK3, no C3 by SK), each piece contributes g <= 3, and 6 - e <= sum g.  The combinatorial type tau(M) = (line pattern
   (dim R_r | dim C_c); for each piece (N?, rank)) takes FINITELY many values, each type is a constructible parameter family, and
   (S6-FO2) <= (BL) + [no R3] + (S6-FO2) for each type family.
   OBSERVED TYPES (numerical, reg2/mech_census.py, log r11_mech_census.log; 187 spaces, (BL) 187/187):
        e = 6 : 128 spaces, 14 line patterns, no genuine part;
        e = 5 : 8  (one R1; in seed_d6_e3_t4 the same genuine direction is R1 in three row pieces and N in five column pieces);
        e = 4 : 34 (one R2 or C2 = single skew deformations), 2 (one row piece N + R1: seed_d6_e3_t1-type), rc45 (free row + two C1);
        e = 3 : 2  (N + R2 on one row pair, R1/C1 elsewhere: clm_p4_d6_defect3_s12, s7);   e = 2 : 4 DOUBLE-BLOCK (R2 + C2), 1 (clm_s3).
   SHAPE AND BASE CHECKS (numerical): every observed genuine R2/C2 block with nondegenerate X_0 has phi = 0 (pure t J; 22 block directions,
   |phi|/|y| <= 2e-8, r11_r2shape2.log); for 29 of 34 single-block spaces the undeformed base (y -> 0) is again a 6-dim level space (a skew
   deformation of a level line-spanned member, the deformation-table setting); 5 are unclear (base level error 5e-6..5e-4 or base dim 4,
   r11_r2base.log).
   WHAT REMAINS (exact list for leaf 11):
     (i)   (BL) itself (NUM 187/187).  Not implied by SK/SK2/SK3/Lemma C (S5): all of them describe pieces once they exist.  Needed: a
           piece-existence statement, e.g. dim Pi(M) = 6, or "every 6-dim level M has a two-row or two-column element outside Lin(M) when
           e < 6" plus induction on 6 - e.
     (ii)  R3: exclude rank-3 three-dim row blocks (cases (alpha), (I), (II) of 19.2).
     (iii) phi != 0 in R2/C2 (not in the deformation table; never observed).
     (iv)  type families NOT yet certified exactly: those with N pieces or R1/C1 attachments (the 19 rows-team (6,3) spaces clm_*, nc_*,
           seed_*: numerically dim T_1 = 9, FO2 7; the e = 5 R1 spaces ext_9..11, dr35_u2_s52_400, dr35_u3_s41_116) -- the deformation
           table deformed only 2-element line groups by t J, i.e. R2/C2 attachments to level bases.
     (v)   (1,1,1|1,1,1) and the 29 hit-free line patterns (e = 6 types without members).
STATUS 00:42: target 4 closed (conic trivial); target 1 partial (reduction R2+R1, incidences (alpha)/(I)/(II), census never rank 3); target 2 statement written (19.3); starting target 3.
STATUS 00:25: (correction: the STATUS line above should read 00:25, not 00:42.)
 19.4 TARGET 3: (1,1,1|1,1,1) IS CLOSED [EXACT]: up to row/column permutations it consists of ONE space, M111, with dim T_1 = 9.
     Tool reg2/p111/incpat.py ROWDIMS COLDIMS [S]: line-spanned pattern with row parts in rows 0.. and column parts in columns 0..; P_2 between a
     row part (row i) and a column part (column m) is x[i] u[m] = 0 for all their elements (mixed 2x2 permanents: sum_{i'!=i} x_i' *
     sum_{d!=m} u_d = x_i u_m), so S[i][m] = 1 (column part vanishes at row i) or 0 (row part vanishes at column m).  For each S: ALL level
     equations (famtool) + sums, saturated (Singular over Q) by the maximal minors of every part (each part of full rank).
     CALIBRATION: (2,2|2) (rows 22, cols 2): S = 01 and 10 NONEMPTY (dim 14 = the DR22 family incl. scalings), 00 and 11 EMPTY -- correct
     (r11 log below); (2,1,1|1,1) running.  (A first version, reg2/p111/inc111.py + cal211.py, named column variables x%d%d, which CLASH with
     famtool's FO variables x%d%d: its "all EMPTY" output (r11_inc111.log, r11_inc111_calibration.log) is INVALID and marked so.)
     RESULT (r11_incpat_111_111.log): 512 incidence matrices: 476 EMPTY, 36 NONEMPTY, each of dimension 6 (= the six element scalings, i.e.
     finitely many spaces); the 36 form ONE S_3 x S_3 orbit (orbit of 000001011 has size 36).  For S = 000001011 the saturated ideal is
     prime and LINEAR (r11_incpat_111_111_S000001011.log):
        M111 = < e_0 (0,0,0,1,-1), e_1 (0,0,-2,1,1), e_2 (0,-3,1,1,1), (1,1,-3,1) e_0^T, (1,-2,0,1) e_1^T, (1,0,0,-1) e_2^T >
     (rows of row elements as 1x5 vectors, column elements as 4-vectors).  M111 is level identically (famtool: 0 nonzero level equations),
     6-dim, single-row dims (1,1,1,0), single-column dims (1,1,1,0,0) (exactly the pattern), numerically (e,E_0,Omega,T_1,FO2) =
     (3,7,2,9,7), Omega = <e_0, 1>.  EXACT: FAMS '111111' (gen_rank.py, dummy parameter), 16x16 minors of the FO matrix: UNIT
     (r11_M111_rank.log) => dim T_1 <= 9 => FO2 <= 8 for every level space containing M111 (and its images under row/column permutations).
     => (1,1,1|1,1,1): (S6-FO2) holds.  This removes the last line-spanned pattern with members from leaf 11 (the round-4 "1 hit in 20" was this
     space).  Next: the same tool on the 29 hit-free patterns (running, r11_incpat_hitfree.log).
STATUS 00:38: (1,1,1|1,1,1) closed exactly (unique space M111, dim T_1 = 9); hit-free patterns running through incpat; (2,1,1|1,1) calibration running.
STATUS 00:36: (correction: the line above is stamped 00:38; actual time of writing 00:36.)
 19.5 THE "HIT-FREE" LINE PATTERNS, exact incidence split (reg2/p111/incpat.py, same method as 19.4) -- IN PROGRESS at the time of writing.
     Calibration of the current code (r11_incpat_calibration.log): (2,2|2), (3|3), (3,1|2) -- all patterns with known members -- give
     NONEMPTY classes; (2,1,1|1,1) (r11_incpat_211_11_v2.log, per-case timeout) also NONEMPTY (dims 8, 9).
     Done (r11_incpat_hitfree.log): EMPTY for (|2,1,1,1,1), (|2,2,1,1), (|2,2,2), (|3,1,1,1), (|3,2,1), (|3,3), (1|1,1,1,1,1), (1|2,1,1,1), (1|2,2,1),
     (1|3,1,1), (1|3,2), (1,1|1,1,1,1), (1,1|2,1,1), (1,1|2,2), (1,1|3,1) -- 15 of the 29 hit-free patterns are EMPTY [exact].
     !! (1,1,1,1|1,1) is NOT empty although CE-1 had 0 hits in 200 starts: incidence class S = 00000111 (rows 0,1: row parts vanish at
     columns 0,1; row 2: part vanishes at column 0, column-1 element vanishes at row 2; row 3: both column elements vanish there) is a
     prime 1-parameter component (r11_incpat_1111_11_S00000111.log):
        u0, u1 in U = {w_0 = w_1 = 0, sum w = 0} with <u0,u1> = 0;  u2 = (0,-3,1,1,1);  u3 = (-4,1,1,1,1);  x0 = (1,1,-2,0);  x1 = (1,-1,0,0)
     (numerically level, 6-dim, exactly the pattern, (e,E_0,Omega,T_1,FO2) = (4,7,2,9,7), reg2/p111/fam1111.py).  EXACT: FAMS '1111_11a'
     (u0 = (0,0,-1-a,1,a), u1 = (0,0,1-a,1+2a,-2-a)) is level identically and its 16x16 minors generate (1) (r11_fam1111a_rank.log);
     the missing point a = infinity ('1111_11inf'): UNIT (r11_fam1111inf_rank.log).  => FO2 <= 8 on this component.  The other
     incidence classes of (1,1,1,1|1,1) and the remaining 13 patterns: r11_incpat_hitfree3.log (orbit representatives only).
     LESSON for leaf 11: "hit-free" (numerical census) does NOT mean empty -- the exact incidence split is needed for every pattern.
STATUS 00:53: (1,1,1|1,1,1) closed; hit-free patterns: 15 EMPTY exactly, (1,1,1,1|1,1) has a 1-parameter family (certified FO2 <= 8 on the first class), remaining classes/patterns running.
 19.6 HIT-FREE PATTERNS, state at the end of round 11 (logs r11_incpat_hitfree.log, hitfree3.log, hitfree4.log; orbit representatives,
     per-case Singular timeout 90-120 s, all < 1 GB).  Of the 29 patterns with 0 CE-1 hits:
     EMPTY [exact] (21): (|2,1,1,1,1), (|2,2,1,1), (|2,2,2), (|3,1,1,1), (|3,2,1), (|3,3), (1|1,1,1,1,1), (1|2,1,1,1), (1|2,2,1), (1|3,1,1),
         (1|3,2), (1,1|1,1,1,1), (1,1|2,1,1), (1,1|2,2), (1,1|3,1), (2|1,1,1,1), (2|2,1,1), (2|2,2), (2|3,1), (3,2|1), (3,3|).
     NOT EMPTY (1): (1,1,1,1|1,1) -- one orbit of classes, a 1-parameter family, dim T_1 <= 9 [exact] (19.5); all other classes empty.
     PARTIAL (7, some classes hit the time limit):  (2,1,1,1|1): 4 classes EMPTY, 4 TIMEOUT;  (2,2,1|1): 4 EMPTY, 2 TIMEOUT;
         (3,1,1|1): 5 EMPTY, 1 TIMEOUT;  (2,2,1,1|), (2,2,2|), (3,1,1,1|) (one class each): TIMEOUT;
         (3,2,1|): TIMEOUT in Singular, but EMPTY by hand [rigorous]: single-row parts of different rows are orthogonal (P_2, 8.4), and
         inside the nondegenerate 4-dim space 1^perp the orthogonal complement of the 3-dim U_0 is 1-dim, so it cannot contain the 2-dim U_1.
     The TIMEOUT classes are queued (QUEUE.md REG2-INCPAT-TMO, 2 GB, <= 1 h per class).  Pre-check added: a part is impossible when its free
     coordinates minus the sum condition are fewer than its dimension (e.g. (1,1,1,1|1,1) class 01101111, resolved that way).
STATUS 01:09: round 11 report: conic trivial; (1,1,1|1,1,1) closed (M111); 21 hit-free patterns empty + (3,2,1|) by hand, (1,1,1,1|1,1) nonempty but certified, 6 partial (queued); 3-dim blocks reduced; mechanism list written.
STATUS 01:11: round 12 started (targets: R3 exactly (II),(I),(alpha); exact N/R1 families incl. the 19 rows-team spaces; piece-existence lemma; INCPAT-TMO verdicts; stale-output check).

# ROUND 12 (reg2, start ~01:12 UTC). Targets: (1) R3 exactly ((II) first); (2) exact families of N/R1 types (19 rows-team spaces); (3) piece
#   existence toward (BL); (4) INCPAT-TMO verdicts.  BRIEF UPDATE 14 check (stale solver output): see 20.0.
## 20. Round 12
 20.0 STALE-OUTPUT CHECK.  gen_rank, gen_rank_defo, lift_gram, omega_e0, certify_defo, incpat, sk3_exact all call Singular with the script on
     stdin and parse the CAPTURED STDOUT of that very call -- no output file is read, so a stale file cannot be picked up.  The only file-based
     solver path is polylib.run_msolve (used for modular runs, labelled [modular]; no exact verdict of mine rests on it): it did NOT delete the
     old output file; FIXED now (os.remove before the call; return code and existence checked).  Exact (char 0) verdicts are unaffected.
     NEW PITFALL found this round: reg2/r3/caseII_oneZ_fixedB.py returned EMPTY stdout (exit 0) from its Singular call although the same script
     run directly prints the full answer -- cause not identified; such runs were therefore executed DIRECTLY (Singular -q < saved script) and
     the scripts are saved next to the logs.  (An empty answer was never read as a verdict.)
 20.1 R3, CASE (II) [exact for two rational B; general B open].  n = e_3 - e_4, W = {sum w = 0, w_3 = w_4}.  SK2 with zeta = 1_S forces
     (Bw)_3 + (Bw)_4 = 0, and the B-space is 4-dim (reg2/r3/bspace_II.py, exact):  B w1 = s a1 + c3 n, B w2 = s a2 + c7 n, B w3 = s a3 + c11 n,
     a1 = (-1/2,-1/2,1,0,0), a2 = (1/2,-1,1/2,0,0), a3 = (0,-1,1,0,0); kernel of the skew part w0 = w1 + w2 - (3/2) w3; rank B = 3 <=>
     s (2c3 + 2c7 - 3c11) != 0.  Every Z of M has z_1 + z_2 in <1, 1_S>; normalise z_3 in <1, n>: 14 coordinates.  Since <P_0, Z> is level for
     every Z in M, the 3-dim N = M/P_0 must be a 3-dim LINEAR subspace of the admissible cone V_B = {Z : <P_0,Z> level} (a cone: the
     conditions are homogeneous in Z).  EXACT for B = (s,c3,c7,c11) = (2,1,3,-1) and (1,-2,5,3) (both rank 3; scripts
     reg2/r3/caseII_B*_minass.sing, logs r12_caseII_VB_B*.log): V_B is the union of 6 prime components, each of dimension 3 and degree 2 inside
     a 4-dim linear space (10 linear forms) -- an irreducible quadric cone, which contains no 3-dim linear subspace (that would be a hyperplane
     of its span, making the quadric reducible).  A linear space inside a finite union of irreducible varieties lies in one of them.  Hence NO
     6-dim level M of case (II) exists for these B.  Numerically (r3/caseII_VB.py) the same picture for random complex B.
     General B: the symbolic run (4 B-parameters + 14 Z + Rabinowitsch, with minAssGTZ) needed > 1 GB (two Singular processes ~1.2 GB) and was
     stopped (r12_caseII_oneZ.log) -- to be queued with a formulation that tests "fibre contains a 3-dim linear space" directly.
 20.2 TARGET 2: the 19 rows-team (6,3) spaces classified (reg2/rows19.py, r12_rows19_classes.log; line pattern + genuine pieces):
       line-spanned (covered by the closed patterns): nc_d6_k1_s2 (2,1|2,1), nc_d6_k1_s23 (1,1,1|3) (exact NC family), nc_d6_k1_s4 (2,1|1,1,1),
         seed_d6_e3_t9 (3|1,1,1), seed_d6_e3_t4 ((3|1,1,1) by the earlier analysis; one row element is single-row only at ~1e-6, so the
         1e-7 census shows e = 5) -- 5 spaces;
       one R2/C2 block on a line pattern: (1|2,1) + R2: nc_s1, nc_s17, nc_s20, seed_t3; (2,1|1) + C2: nc_s21; (1|3) + R2: seed_t0, t2, t5, t7;
         (1,1|2) + R2: seed_t1, t6 -- 11 spaces; NOT deformations of level bases in the deformation-table sense (r11_r2base.log: their
         undeformed bases are not level), so NOT yet covered;
       clm_p4_d6_defect3_s3, s7, s12 (e = 2, 3; N + R1/R2 pieces) -- 3 spaces, not covered.
     Exact families for the 14 uncovered spaces: NOT done this round (each type needs an incpat-style split with a block; the (1|3) types contain
     a full free COLUMN 1^perp (x) e_c, which simplifies them: every row/block vector vanishes at column c by P_2).
 20.3 TARGET 3: piece existence -- data and a trivial lemma.  (PE0) [rigorous, trivial] P_kl = ker(pi_rr' on M), so
     dim P_kl >= 6 - dim pi_r(M) - dim pi_r'(M): two rows with projection dims summing to <= 5 force a two-row piece on the complementary pair.
     Census (reg2/piece_stats.py, r12_piece_stats.log): sorted row-projection dims are tiny -- the two smallest sum to <= 5 in 184 of 187 spaces
     (exceptions (3,3,3,3) x 1 and (3,3,3,4) x 2), and every space has max two-row piece >= 2 or max two-column piece >= 2.  A real lemma would
     bound dim pi_r(M) from the level equations (e.g. "dim pi_r(M) + dim pi_r'(M) <= 5 for some pair"); no proof yet.
STATUS 01:39: case (II) closed for two rational B (quadric-cone argument), general B open; 19 rows-team spaces classified (5 covered, 14 not); piece-existence data; stale-output check done.
 20.4 INCPAT-TMO verdicts (pool run, log r11_incpat_tmo_big.log, 2 GB) + hand reductions:
     (2,1,1,1|1): 0111 EMPTY (pre-check), 1000 EMPTY, 1011 EMPTY (pre-check), 1001 Singular "halt" at 2 GB -> OPEN;
     (2,2,1|1): 011 EMPTY, 110 "halt" at 2 GB -> OPEN;
     (3,1,1|1) 101: out of memory at 2 GB in the pool, but EMPTY [rigorous reduction + exact]: x vanishes at rows 0, 2 => x ~ (0,1,0,-1);
         U_1, U_2 lie in the line U_0^perp cap 1^perp = C n (1^perp is nondegenerate, dim U_0 = 3), u_1 perp u_2 => n isotropic; an
         isotropic n perp U_0 lies in U_0 (else U_0 + Cn = 1^perp and n perp 1^perp, n = 0), so U_0 = n^perp cap 1^perp, n_0 = 0 (incidence);
         M is determined by n and its level ideal saturated by n is (1) (reg2/p111/hand311_101.py/.sing, r12_hand311_101.log);
     (3,1,1,1|): EMPTY [same reduction, n general isotropic; reg2/p111/hand3111.py/.sing, r12_hand3111.log];
     (2,2,1,1|), (2,2,2|): pool run in progress at the end of this round.
     => hit-free patterns now: 23 EMPTY (+ (3,2,1|) by hand = 24 counting it), (1,1,1,1|1,1) nonempty-and-certified, OPEN: (2,1,1,1|1) [1 class],
        (2,2,1|1) [1 class], (2,2,1,1|), (2,2,2|).  The two-plane patterns should yield to the same orthogonality reduction (two 2-dim
        mutually orthogonal parts in the 4-dim 1^perp must intersect in an isotropic line or span it).
STATUS 01:41: round 12 report (short round before Lean window 2): R3 (II) closed for two rational B; rows-team spaces classified; (3,1,1|1) and (3,1,1,1|) closed; stale-output check done.
 20.5 ORTHOGONALITY REDUCTIONS for the all-row hit-free patterns [rigorous + exact where stated].  V := 1^perp (C^5), nondegenerate, dim 4;
     single-row parts of different rows are mutually orthogonal (P_2).  Facts: (i) an isotropic line orthogonal to a 3-dim subspace W of V lies in
     W; (ii) for U_0 perp U_1 (2-dim each) with U_0 cap U_1 = C a, the radical of W = U_0 + U_1 is C a (a perp both; rad(W) <= 1-dim);
     (iii) U_0 cap U_1 = 0 gives U_0 (+) U_1 = V, so any further part is perp V, i.e. zero.
     (2,2,2|) EMPTY [rigorous + exact]: by (iii) all pairs intersect; if U_0 cap U_1 = C a then U_2 lies in the 1-dim (U_0+U_1)^perp cap V --
       impossible; so U_0 = U_1 = U_2 = T, a totally isotropic plane (T^perp = T), and P_3 (2 T(u,u',u'') for pairwise orthogonal sum-zero
       vectors) requires the cubic sum_c u_c^3 to vanish on T.  Exact: {u, v spanning an isotropic sum-zero plane with vanishing cubic},
       saturated by the 2x2 minors, is (1) (reg2/p111/hand222.sing, r12_hand222.log).
     (2,2,1,1|): reduced to case A (U_0 = U_1 = T isotropic, u_2, u_3 in T) and case B (U_0 cap U_1 = C a, u_2 ~ u_3 ~ a by (i),(ii)); the two
       exact checks (reg2/p111/hand2211.py -> hand2211_A/B.sing) halted at the 1 GB cap -> queued REG2-HAND2211 (3 GB).
     Still open among the hit-free patterns: (2,1,1,1|1) class 1001, (2,2,1|1) class 110 (pool halts at 2 GB), (2,2,1,1|) (queued);
     (2,2,2|), (3,1,1|1), (3,1,1,1|), (3,2,1|) closed this round.
STATUS 02:05: round 12 report; no own jobs running (Lean window 2); queued REG2-R3-II-GENERIC, REG2-HAND2211.
STATUS 02:07: round 13 started (targets: R3 (I), (alpha), special strata of (II); 3 open hit-free items; rows-team families / FL check; empty-output wrapper cause). Lean window 3 open -> light runs only.

# ROUND 13 (reg2, start 02:07 UTC; Lean window 3 open -> light runs only).  Targets: (1) R3 (I), (alpha), special strata of (II); (2) the 3 open
#   hit-free items; (3) rows-team families / FL, PFC; (4) the empty-output wrapper.
## 21. Round 13
 21.0 THE EMPTY-OUTPUT WRAPPER, CAUSE FOUND (target 4).  reg2/r3/caseII_oneZ*.py printed r.stdout[:6000]; when a script loads BOTH elim.lib and
     primdec.lib, Singular first prints ~6000 characters of "// ** redefining ..." warnings, so the answer (at the end of the 7884-character
     output) was cut off -- Singular itself worked (a standalone test returns the full output either way, 106-145 s).  Other drivers: gen_rank
     loads matrix.lib + primdec.lib (no redefinition warnings, verified: no "redefining" in any r8-r10 evidence log), lift_gram loads matrix.lib
     only, omega_e0 loads primdec.lib only in its print-the-uncovered-locus branch, incpat loads elim.lib only (dump mode prints everything),
     sk3_exact loads nothing -- none of their verdicts can be truncated this way.  Rule from now on: strip "// **" lines before truncating.
 21.1 ALL 29 HIT-FREE LINE PATTERNS ARE SETTLED [rigorous reductions + exact]: 28 EMPTY, and (1,1,1,1|1,1) non-empty with FO2 <= 8 certified.
     Common tools (V = 1^perp nondegenerate of dim 4; single-row parts of different rows are orthogonal, P_2):
       (O1) orthogonal 2-dim parts with U_0 cap U_1 = 0 span V, so a further part is 0;  (O2) if U_0 cap U_1 = C a then (U_0+U_1)^perp cap V
       = C a = rad(U_0+U_1);  (O3) a totally isotropic plane T has T^perp cap V = T;  (O4) in a nondegenerate plane, three nonzero pairwise
       orthogonal vectors lie on one isotropic line;  (PS) POWER SUMS: if sum v^k = 0 for k = 1..4 (resp. k = 1..3 and v_0 = 0) then v = 0 or
       its entries are 5 distinct numbers (resp. v = c(0,1,i,-1,-i) up to the order of the other columns) -- Newton: the entries are the roots of
       x^5 - e_5 (resp. x (x^4 - e_4)); then 1, v, v^2, v^3 are linearly independent.
     (2,2,1,1|) EMPTY: by (O1) U_0 cap U_1 != 0.  A: U_0 = U_1 = T (O3), u_2, u_3 in T.  A1: u_2, u_3 independent -> P_3 makes the cubic vanish
       on T: the (2,2,2|) system, empty (hand222, round 12).  A2: u_2 ~ u_3 ~ u: u in T is isotropic with sum u^3 = 0 (P_3, rows 0,1,2 with
       x = y = u) and sum u^4 = 0 (P_4, rows 0..3); by (PS) T = <u,v> with v in {sum = 0, <.,u> = 0, sum u^2 . = 0, sum u^3 . = 0} = C u:
       contradiction.  B: U_0 cap U_1 = C a, u_2 ~ u_3 ~ a (O2); a: sum a^k = 0 for k = 1..4 (isotropic, P_3, P_4), p in U_0 satisfies the four
       linear conditions sum p = <a,p> = sum a^2 p = sum a^3 p = 0, hence p in C a by (PS): contradiction.  [rigorous]
     (2,2,1|1) class 110 EMPTY: x ~ (0,0,1,-1); cases A (U_0 = U_1 = T, u_2 = a in T) and B (U_0 = <a,p>, U_1 = <a,q>, u_2 ~ a); in both, a is
       isotropic, a_0 = 0, sum a^3 = 0, so a = (0,1,i,-1,-i) up to S_4 (PS); exact: all level equations over Q(i), saturated, give (1) in both
       cases (reg2/p111/hand221_110.py -> hand221_110_{A,B}.sing; log r13_hand221_110.log).
     (2,1,1,1|1) class 1001 EMPTY: x ~ (0,1,-1,0); u_1, u_2, u_3 in U' = U_0^perp cap V, pairwise orthogonal.  U_0 nondegenerate: all u_i on an
       isotropic line C n (O4), n_0 = 0, sum n^3 = 0 -> n = (0,1,i,-1,-i) (PS); U_0 inside {sum = <.,n> = sum n^2 . = sum n^3 . = 0} (P_2, P_3,
       P_4), a line: contradiction.  U_0 totally isotropic (U' = U_0): rank 1 as before; rank 2: sub-cases D1b (u_1, u_2 independent) and D1c
       (u_2 ~ u_1, u_3 independent).  U_0 of rank 1 (rad C r, U' = <r,s>, <s,s> != 0): at most one u_i has an s-component; none -> as before;
       exactly one: D2s3 (u_3 special) and D2s1 (u_1 special; u_2 is symmetric), with r = (0,1,i,-1,-i) (r isotropic, r_0 = 0, sum r^3 = 0 from
       P_3 with t = r in U_0).  Exact: D1b, D1c, D2s3, D2s1 all (1) (reg2/p111/hand2111_1001.py; log r13_hand2111_1001.log).
     => with rounds 11-12: (2,1,1,1|1) all 8 incidence classes empty, (2,2,1|1) all 6 empty.  LEAF 11 ITEM (v) IS CLOSED: (S6-FO2) holds for
        EVERY line-spanned 6-dim 4x5 level space (15 patterns with members [rounds 2-5], (1,1,1|1,1,1) [M111], (1,1,1,1|1,1) [family], and the 28
        other patterns are empty).
STATUS 02:16: all 29 hit-free patterns settled (28 empty + (1,1,1,1|1,1) certified) -> every line-spanned pattern closed; wrapper cause found (warning truncation).
 21.2 ROWS-TEAM SPACES RE-CLASSIFIED (tolerance).  These 19 files are stored to ~1e-6 (level error 1e-13, but line elements appear only at
     tolerance ~1e-4); the 1e-7 classification of 20.2 UNDER-COUNTED line elements.  With tolerance 1e-4 (reg2/rows19b.py, r13_rows19_tol1e-4.log):
       line-spanned (6): nc_s1 (2,1|2,1) [was "R2"], nc_s2, nc_s23, nc_s4, seed_t4, seed_t9 -- covered by the closed patterns;
       full free column on four rows + R2 (6): seed_t0, t2, t5, t7, clm_s7, clm_s12 (column part 1^perp of C^4, i.e. {x : x_r = 0, sum = 0} in L)
         -- covered by stage3's LEMMA PFC (a level space containing a free column on four rows has dim <= 8 unless some 5-dim 4x5 level space
         has defect line C(1,1,1,1,-4); that remaining (5,1)_{m0} case is PROOF-MAP leaf 4).  Theorem FL itself does not apply (FL needs the
         full 4-dim 1^perp of C^5 in one line of L);
       one R2 block on a line pattern (7): (1|2,1)+R2: nc_s17, nc_s20, seed_t3;  (2,1|1)+C2: nc_s21;  (1,1|2)+R2: seed_t1, t6, clm_s3.
     All 19 numerically (9,3,7).  The 7 block spaces are what 21.4 is about.
 21.3 (3 open hit-free items) -> 21.1.
 21.4 !! GAP IN THE DEFORMATION TABLE (rounds 8-10) FOUND AND BEING CLOSED.  reg2/gb/defo_scan.py only deformed single-line parts given by
     EXACTLY TWO basis elements ("2-element groups"); families whose 2-dim parts are written with SPANNING SETS (U0span: 4 vectors for a plane)
     were never deformed along those parts: 213, 2121V0/Vni/Vnii(+s0, xinf), 11121A1/B1/B2, 2211BD, 21111ACD/aa/ab/II.  New tool
     reg2/gb/defo_scan_span.py keeps two generically independent spanning elements and zeroes the others (valid on a Zariski-open set of
     parameters; special loci need another pair).  Result (r13_defo_scan_span_2121V0.log, r13_defo_scan_span_all.log), deformations of the
     spanning-set row parts:
       LEVEL FOR ALL: 213 row 0->1 (= the known 213def family, closed in round 8), 2121Vni row 0->1, 2121Vnii_xinf row 0->1, 2211BD row 0->1.
       special loci: 213 row 0->2/3 (u1+2u2+1 and 4 points); 2121V0 row 0->1 (s^2+s+1, s+1), 0->2/3 (s+1); 2121Vni row 0->2/3 (u1+2u2+1,
       (1,1)); 2121Vnii row 0->1 (s^2+s+1, s+1), 0->2 ((p,s), s+1), 0->3 ((p+1,s), s+1); 2121Vnii_s0 row 0->2 (p), 0->3 (p+1); 2121Vnii_xinf
       row 0->2/3 (s+1); 2211BD row 0->2/3 (v1+2v2+1, (1,1)); 21111ACD row 0->1 (s^2+s+1, s+1), 0->2/3 (s+1); 21111ab row 0->1 ((s^2+s+1,q),
       s+1), 0->2 (s+1, (q^2+2, s)), 0->3 (s+1); 21111II row 0->1 (s^2+s+1, s+1), 0->2 (s+1, s), 0->3 (s+1).
       (column spanning sets: 11121A1/B1 col 4->3 as before; no new column cases.)
     Numerically all four level-for-all families are (9,3,7) (defo_inv on the basis versions FAMS '<fam>_b', gen_rank.py), Omega = <1, e_c>,
     d = d^4 (resp. d_1 for 2211BD) -- so dim T_1 <= 9 is the target; the 7 rows-team block spaces of 21.2 are presumably members.
     Exact certificates: in progress (21.5).  The double-deformation scan (16.4) used the same group rule and must be redone for these parts too.
STATUS 02:25: deformation-table gap found (spanning-set parts never deformed) -> new scan; rows-team re-classified (6 line-spanned, 6 PFC, 7 block); certificates of the new families started.
 21.5 THE NEW DEFORMATIONS, status [exact unless stated].  Basis versions FAMS '<fam>_b' (spanning pair 1), '_b2' (last pair), '_b3' (pair 2,3)
     in gen_rank.py; three charts cover every parameter value where the plane is 2-dim (chart 1 degenerates on u1+2u2+1 = 0 resp. s = -1,
     chart 2 on u1 = 1 resp. s = 1, both only at (1,-1), where chart 3 is used).  Triviality test reg2/gb/defo_trivial.py (rank[M(0);M(t)]).
     - Loci s^2+s+1 = 0 (and (s^2+s+1, q) for 21111ab, (q^2+2, s or s+1) for 21111ab): the deformation is TRIVIAL (M(t) = M(0), det G = 0)
       [numerical test, r13_defo_trivial*.log]; loci where the chosen pair degenerates (base dim 5) are chart artefacts.
     - Genuine special points, all certified (certify_defo.py: generic dim T_1 over Q(t), minors, gcd of 3x3 minors; r13_cd_*.log,
       r13_pt_*.log, summary r13_cd_summary.log / r13_pt_summary.log):
         213 row 0->2 and 0->3 at (u1,u2) = (1,1), (1,-3), (0,-1), (0,0) [chart 1] and (-1/3,-1/3), (-3,1), (-1,0) [chart 2]: dim T_1 <= 9;
         2121Vnii row 0->2 at (s,p) = (0,0) [chart 1], (-1,0) [chart 2]; row 0->3 at (0,-1), (-1,-1): dim T_1 <= 9;
         21111II row 0->2 at s = 0 [chart 1], s = -1 [chart 2]: dim T_1 <= 9;
         2121Vni row 0->2 at (1,1): t = 0 only; row 0->3 at (1,1): dim T_1 <= 9;
         2211BD row 0->2 and 0->3 at (1,1): (10,4,8), 15x15 minors UNIT and gcd of the principal 3x3 minors = 414720 (constant): rank q >= 3;
         at (1,-1) [chart 3]: row 0->2/0->3 are NOT level (no deformation); row 0->1 level with dim T_1 <= 9 for t != 0.
     - Level-for-all families: 213 row 0->1 = 213def (closed in round 8); 2121Vnii_xinf row 0->1 (s,t): 16x16 minors leave s = -1 (chart 2:
       t = 0 only), s^2+s+1 (exact: t = 0 only at s = omega), t = 0  => CLOSED (r13_xinf_*.log);  2121Vni row 0->1 and 2211BD row 0->1
       (2 parameters + t): minors runs in progress / queued (REG2-DEFOSPAN).
     - Second deformations on the basis versions (defo_scan2, r13_defo_scan2_span.log): 2121Vni_b row 0->1 + col 4->1 at (u1,u2) = (0,-1/2);
       2211BD_b row 0->1 + row 1->0 on the BD conic; 2121V0_b col 4->3 + row 0->1/2/3 at s^2+s+1, s+1 -- to be certified/tested next.
STATUS 02:40: new deformation families: special points all certified, 2121Vnii_xinf row 0->1 closed; two 2-parameter families running.
 21.6 R3, CASES (I) AND (alpha) (target 1) -- set up, not decided.  reg2/r3/r3_cone.py builds, for a rational point (n, B), the admissible
     cone V_B of the case (Z normalised by z_3 in <1, m>, z_1 + z_2 restricted as the case demands) and writes a Singular script that lists its
     components (dim, degree, number of linear forms), so the cone argument of 20.1 can be applied.  B-spaces (exact, sympy): case (I) with
     n = (1,2,3,-6,0): 4-dim; case (alpha) with n = (1,2,3,4,-10): 6-dim (all of {B : b skew}).  Scripts r3_cone_I_1.sing, r3_cone_alpha_1.sing;
     the case-(I) run halted at the 700 MB virtual cap of the Lean window (r13_r3_cone_I_1.log) -> queued REG2-R3-CONE.
     Second deformations (21.5) re-checked in the second chart: every locus found lies on the degeneracy locus of its own chart and does not
     reappear in the other chart, except the BD conic and s^2+s+1, where the second deformation is TRIVIAL (rank [M1; M2] = 6; r13_defo_scan2_
     span*.log, defo2_trivial.py).  So no new double-deformation family.
 21.7 SUMMARY FOR LEAF 11 after round 13.  (a) line-spanned: ALL patterns closed (21.1).  (b) the deformation table was incomplete (21.4);
     after the re-scan, OPEN are only the two 2-parameter level-for-all families 2121Vni row 0->1 and 2211BD row 0->1 (numerically (9,3,7);
     queued REG2-DEFOSPAN / -MINORS); all special points and 2121Vnii_xinf row 0->1 are certified, the other loci are trivial or chart artefacts.
     (c) rows-team spaces: 6 line-spanned, 6 under Lemma PFC (modulo leaf 4), 7 presumably in the families of (b).  (d) R3: (II) at two rational
     B; (I), (alpha) and the generic computations queued.  (e) (BL) and the N/R1-type families: unchanged.
STATUS 02:52: round 13 report; no own jobs running; queued REG2-R3-CONE, REG2-DEFOSPAN(-MINORS).
STATUS 02:53: round 14 started (targets: the two open families' certificates; rows-team membership; R3 cones; N/R1 families and (BL)).

# ROUND 14 (reg2, start 02:53 UTC; Lean window 3 still open -> light runs).  Targets: (1) the two open families; (2) membership of the 7 one-block
#   rows-team spaces; (3) R3 cones; (4) N/R1 families, (BL).
## 22. Round 14
 22.1 MEMBERSHIP OF THE ROWS-TEAM SPACES (target 2) [numerical, reg2/gb/fam_member.py: Grassmannian least squares over the family parameters for
     every signature-preserving row/column permutation; logs r14_rows_membership*.log].
       seed_t0, t2, t5, t7, clm_s7, clm_s12  in 213def (= 213_b row 0->1, closed in round 8), residual 2e-7 (file precision), t ~ 1e-3;
       nc_s21  in 2121V0 col 4->3 (closed in round 8), residual 7e-15;
       nc_s17  in 2121Vni row 0->1 (NEW family of 21.4, open), residual 8e-8;
       nc_s20, seed_t3  NOT in any 2-dim-part deformation, but their undeformed bases are LEVEL (3|2,1) spaces: they lie in the NEW family of
         22.2 (3-dim row part of (3|2,1)a deformed with S ~ (-1,-1,3)), residual 1e-15;
       seed_t1, t6, clm_s3  ((1,1|2)+R2): not in 211iii row 0->2 (residual 1.7); candidate: the 3-dim row-part deformation 312_d3_1 (22.2).
     (The 6 "PFC" spaces are thus covered UNCONDITIONALLY by 213def; PFC is not needed for them.)
 22.2 !! SECOND GAP IN THE DEFORMATION TABLE: 3-DIM PARTS.  A 3-dim single-line part V (rows: inside 1^perp of C^5; columns: 1^perp of C^4)
     admits skew deformations of rank 2, v -> v + e_tgt (B v) with B = adj(G) S, S skew 3x3 (3 parameters s); these were never scanned
     (defo_scan / defo_scan_span only deform 2-dim parts).  New scan reg2/gb/defo_scan3.py (components of the level ideal in (base, s) not
     inside {s = 0}; log r14_defo_scan3_all.log):
       321a row 0 -> 1, 2, 3: S ~ (-1,-1,3) for EVERY p (a 2-parameter family (p, t) per target); row 0 -> 2 at p = 0 and row 0 -> 3 at p = -1
         with S FREE;
       3111 row 0 -> 1 at p = -1/2, S ~ (1,-3,1); row 0 -> 2 at p = -2 (S ~ (1,-3,1)) and p = 0 (S ~ (-1,-1,3)); row 0 -> 3 at p = 1, -1;
       312 row 0 -> 1: S ~ (1,1,1) for EVERY (m1,m2); row 0 -> 2/3: conic and special components;
       213 col 4 -> k (the 3-dim column part): point families with fixed S;  blockall row 0 -> k: special (w, p) loci.
     Numerically all are genuine (rank [M0; M] = 8), level, (9,3,7) (reg2/gb/defo3_num.py).  FAMS '321a_d3_<k>', '312_d3_1' (gen_rank.py).
     So the deformation table must be completed by: certificates for these families, the 3-dim-part deformations of the remaining
     patterns ((3|3), (1,1,1|3) NC family, (3,1|1,1), (3|1,1,1) done as 3111), and second deformations involving them.
STATUS 03:19: rows-team: all 7 block spaces identified (2 closed families, 2121Vni row 0->1, and NEW 3-dim-part deformations); second gap (3-dim parts) found and scanned.
 22.3 3-DIM-PART DEFORMATIONS, certificates [exact] (gen_rank.py; families '321a_d3_<k>', '<base>@<fixed>@<kind,idx,tgt>@<S direction>'
     built on the fly by _defo3/_fixbase; logs r14_rank_*.log):
       (3|2,1)a row 0 -> 1, 2, 3 along S ~ (-1,-1,3), all (p, t): level identically; 16x16 minors leave t = 0 points, plus for target 2 the
         points (p,t) = (-1,-1/4), (-1,-1/44) and for target 3 the line p = -1: at p = -1 both families are UNIT => CLOSED;
       (3|2,1)a row 0 -> 3 at p = -1 and row 0 -> 2 at p = 0 with S FREE (s1,s2,s3): level identically; minors leave finitely many S-directions
         (and points on them); along every one of them (12 runs) only t = 0 or UNIT => CLOSED;
       (3|1,1,1) row 0 -> 1 at p = -1/2, 0 -> 2 at p = -2 and 0, 0 -> 3 at p = 1 and -1 (fixed directions): all UNIT => CLOSED.
       Not yet: (3,1|2) row 0 -> 1 along S ~ (1,1,1) for all (m1,m2) (3 variables; running), its conic components, (2,1|3) column-part points,
       BLOCK loci, and the 3-dim parts of (3|3), (1,1,1|3), (3,1|1,1) (families not in FAMS with exact 3-element groups).
 22.4 THE N TYPE IS REAL (rows-team seed_t1, t6, clm_s3).  Their rows-(1,2) piece = a non-sum-zero element N (sum x != 0,
     <x,y> = -(sum x)^2, residual 1e-12) + a rank-one isotropic R1 element; undeforming either row gives a NON-level space (level error ~50,
     r14_base_check_t1.log), so these spaces are not skew deformations of a level line-spanned space at all.  An exact family for the type
     "(1,1|2) + N + R1" has to be built from scratch (next round).  All census R1 elements are RANK-ONE ISOTROPIC: e_r x + e_j y with y || x,
     <x,x> = 0 (ext_9/10/11, dr35_u2_s52_400, dr35_u3_s41_116, RANK-ONE dr35_u3_s41_29; r14 log of /tmp/r1elem) -- a candidate lemma
     ("R1 => rank one") for the mechanism list.
 22.5 (BL) -- what would force pieces.  Data so far: every census space is a line-spanned space, a (often tiny, t ~ 1e-3) skew deformation of
     one along a 2- or 3-dim part, or contains N / rank-one R1 pieces.  A proof route that fits all of it: (i) show that a 6-dim level M has
     some line element (a single-row or single-column element) unless it has a two-row/two-column N-piece; (ii) induct on 6 - e by splitting
     off a line element L and studying M/L inside the 4x5 "quotient" -- the SK/SK2/SK3 lemmas then describe the pieces that the level equations
     force around L.  Step (i) is the real content; the defect inequality (Branch 1) is the natural input (it bounds dim M against the defect
     space, and line elements correspond to defect directions).  Nothing proved yet.
STATUS 03:35: 3-dim-part deformations of (3|2,1)a and (3|1,1,1) closed exactly; (3,1|2) running; N type confirmed (needs a family); (BL) route sketched.
 22.6 (2,1|3) COLUMN-PART (3-dim) DEFORMATIONS CLOSED [exact, r14_rank_213_col3.log]: the 4 point families (fixed S directions) UNIT; the
     lines u1 = 0 (col 4 -> 1), u2 = 0 (col 4 -> 2), u1+u2+1 = 0 (col 4 -> 3, FAMS '213_c3line' with the line as relation) along S ~ (1,1,1):
     16x16 minors leave t = 0 and finitely many base points / t-values; at each of those base points the full t-line is UNIT.
     REMAINING 3-dim-part items: (3,1|2) row 0 -> 1 along (1,1,1) (queued REG2-DEFO3-312) and its conic components; BLOCK (blockall) loci;
     the 3-dim parts of the patterns not in FAMS with exact 3-element groups ((3|3), (1,1,1|3), (3,1|1,1)).
STATUS 03:37: round 14 report; no own jobs running.
STATUS 03:38: round 15 started (queued certificates; remaining 3-dim items + completeness argument; N-type family; R1 rank-one; (BL)).

## 23. Round 15
 23.0 The four (2,1|3) point runs on u1+u2+1 = 0 (22.6) print "0 level equations" (level identically) -- checked, r15_213_line_levelcheck.log.
 23.1 (3|3) [exact]: FAMS '33' (unique member).  defo_scan3: row 0 -> 1, 2, 3 LEVEL FOR ALL S (3 free parameters); col 4 -> k along
     S ~ (3,2,1).  The four column families: 16x16 minors UNIT (r15_rank_33.log).  Row families with free S: run '33_S_row1' (below).
 23.2 THE N-TYPE SPACE [exact]: with the rigid part observed in all three rows-team N spaces fixed over Q(w) (row 0 line (0,1,w,w^2,0), row 3
     line (0,w^2,1,w,0), R1 = (e_1 - e_2)(x)(0,w,1,w^2,0)), the level system for (column-0 plane V, N = e_1 a + e_2 b) saturated by rank V = 2
     and sum a != 0 is ONE linear prime component (reg2/p111/ntype.py/.sing, r15_ntype.log): V = {x_1 = x_2, x_0 = -2x_2 - x_3} and N unique
     modulo R1 -- a single space ntype1 (FAMS 'ntype1', N = e_1 (0, w+2, 1-w, 0, -1) + e_2 (0, w^2-1, w-1, 0, 1)).  Exact: level (all 25 level
     polynomials reduce to 0 mod w^2+w+1, r15_ntype1_levelcheck.log); 15x15 minors UNIT => dim T_1 <= 10 (r15_ntype1_rank.log).  Numerically
     (10,4,8) with dim E_0 = 8 (the rows-team files read (9,3,7) -- at their precision ~1e-6 the rank detection is unreliable).  OPEN: an exact
     rank q >= 3 (lift_gram needs dim Omega = 3; here Omega = <1, e_0>), and whether the rigid part is forced (general N-type system).
 23.3 COMPLETENESS -- WHAT THE LIST IS (target 2, for verify2).  The finite statement is Theorem 19.3 (conditional on (BL)): M = Lin(M) +
     genuine parts of types R1/C1, R2/C2, N, [R3].  The objects to verify are the COMBINATORIAL TYPES tau = (line pattern (a_r | b_c), e = sum,
     the genuine parts with their row/column pairs, types and incidences) with e + (genuine dimension) = 6; for each tau the exact solution set of
     the level equations must be known (as incpat does for e = 6).  The deformation scans are only a way to FIND components of these solution
     sets: they find exactly the spaces obtained from a LEVEL line-spanned space by skew-deforming one part (2-dim: t J; 3-dim: adj(G) S) or two
     parts (second scan).  They cannot be complete:
       (G1) parts written as spanning sets -- found and repaired (round 13);  (G2) 3-dim parts -- found and mostly repaired (rounds 14-15);
       (G3) other skew shapes B = t J + phi (phi into X^perp cap 1^perp mod Lambda) -- never observed (22 directions, round 11), NOT excluded;
       (G4) spaces whose base (genuine part killed) is NOT level -- they are not deformations at all; this OCCURS: the N type (23.2);
       (G5) simultaneous deformations of >= 2 parts beyond the scanned pairs (the second scan used 2-element groups only; spanning-set and 3-dim
            second deformations were checked only for the new families of rounds 13-14);
       (G6) 4-dim parts: full free rows are outside (S6-FO2) (Theorem FL); 4-dim column parts do not exist (1^perp of C^4 is 3-dim).
     So a "third gap" is not hypothetical: (G4) is real and (G3), (G5) are open.  The COMPLETE verification is type-by-type: e = 6 is DONE
     (rounds 2-13, all 45 patterns); for e <= 5 only the components reachable by deformation scans are verified.  What verify2 can check now:
     (i) the e = 6 list (45 patterns, incpat logs + hand reductions); (ii) the deformation families listed in 21.5, 22.3, 22.6, 23.1 with their
     certificates; (iii) the explicit statement that e <= 5 is NOT exhausted.  Next: an incpat-style exact solver for e = 5 (one genuine
     element R1/C1/N attached to a line pattern), using the orthogonality/incidence reductions; the type count is finite but large (~40 line
     patterns x positions x 3 types), so reductions (incidences, (PS), the conjectured "R1 => rank one") are essential.
STATUS 03:46: (3|3) column families closed, N-type space ntype1 found exactly (dim T_1 <= 10; rank q pending); completeness argument written (type-by-type; deformation scans incomplete in principle: (G3)-(G5)).
 23.4 ntype1 IS CLOSED [exact]: reg2/gb/q_rank_exact.py (sympy over Q(sqrt(-3))): dim T_1 = 10 and rank q_Y = 5 for two Y in M
     (r15_ntype1_qrank.log)  =>  FO2 bound <= 10 - 3 = 7.  [SUPERSEDED round 16 (verify2 COMPUTE-ERRATA [R]): the round-15 tool OVERestimated the rank (sympy Matrix.rank on sqrt(-3) expressions); the corrected DomainMatrix computation gives rank q_Y = 4 for three Y (r16_ntype1_qrank_fixed.log), so FO2 <= 10 - 2 = 8 -- ntype1 is still closed.]  The three rows-team N spaces match ntype1 up to row/column permutations and
     w <-> w^2 with residual 3.4e-6 (fam_member, r15_ntype_membership.log) -- at the files' precision, but slightly above it.
 23.5 THE N TYPE IS PROBABLY A 2-PARAMETER FAMILY through ntype1: the Jacobian of the level equations in the 34 coordinates of the type
     "(1,1|2) + N + R1" at ntype1 has rank 23, kernel 11 = 9 (gauge: 3 scalings, GL_2 on the column plane, N -> mu N + nu R1) + 2
     (r15_ntype_tangent.log).  Following these directions numerically (LM with gauge fixing) did not converge cleanly (residual ~1e-6;
     r15_ntype_follow.log); the rows-team files (generic (9,3,7) at their precision, 3e-6 from ntype1) suggest generic members with
     dim T_1 = 9.  The general exact system (34 unknowns) is the next step; fixing the rigid part is NOT enough (it gives only ntype1).
 23.6 "R1 => rank one isotropic": still a conjecture.  Evidence: all 5 census R1 elements and the R1 element of ntype1.  The linear
     consequences of SK2 for a 1-dim block give only T(x, y, zeta_Z) = 0 for every Z, i.e. x o y orthogonal to the zeta-span plus 1; this
     does not force y || x.
 23.7 (3|3) row 0 -> k with free S: numerically these spaces lie in the certified family 213def (Grassmannian fit residual 1e-15 at a random
     S, 7e-9 at S = (1,0,0); r15_33_in_213def.log); an independent exact certificate is queued (REG2-33ROW).
STATUS 03:54: round 15 report; no own jobs running.
 23.8 SIZE OF THE LIST (reg2/types_e5.py): e = 5 has 29 line patterns (parts <= 3) and 296 types (pattern x position of the genuine pair x
     genuine type R1/C1/N), before incidence splits; e <= 4 adds blocks (R2/C2) and pairs of genuine elements -- several thousand systems.
     So the type-by-type verification is finite but large: it needs (a) an automatic incpat-style generator with the orthogonality/incidence
     reductions of 21.1, and/or (b) structural lemmas that cut the list (R1 => rank one isotropic; phi = 0 for R2; a (BL)-type existence lemma).
     This is the honest status of leaf 11: e = 6 done; e <= 5 = verified families (deformation table, ntype1) + an explicit, still unexhausted
     type list.
STATUS 03:55: round 16 started (automatic e=5 type solver; cutting lemmas; general N-type system; pool certificates).

## 24. Round 16
 24.0 CORRECTION (verify2, COMPUTE-ERRATA [R]): ntype1 has rank q_Y = 4, not 5.  reg2/gb/q_rank_exact.py was REWRITTEN to work end-to-end in
     the number field QQ<sqrt(-3)> with DomainMatrix (no symbolic simplification): dim T_1 = 10, rank q_Y = 4 for three Y (r16_ntype1_qrank_
     fixed.log), agreeing with verify2.  FO2 <= 10 - 2 = 8, so ntype1 stays closed.  The round-15 tool was used for ntype1 only; no other
     verdict rests on it.  (sympy Matrix.rank on sqrt(-3) expressions overestimated the rank -- the dangerous direction.)
 24.1 AUTOMATIC e = 5 TYPE SOLVER, pre-check measure (target 1).  reg2/e5/inctype.py (types: pattern x genuine pair position x R1/C1/N;
     incidence classes orbit-reduced under the type's symmetry).  Pre-checks without any Groebner basis (r16_e5_precheck.log, all 296 types):
       (P2) orthogonality of the LINE parts alone ((3,>=2) row parts; a 3-dim column part with any other column part; (2,2) column parts):
            kills 66 of 296 types;
       (P1) incidence + sum (a part forced below its dimension): kills 214 of the 1370 incidence classes of the remaining 230 types;
       1156 classes survive the pre-checks.
     So pure orthogonality/incidence cuts only ~22% of the types and ~16% of the classes.  A direct Groebner run per class (all unknowns at
     once, ~30 variables) times out at 30 s in the test cases (r16 test: (2,1|2)+R1 on rows (0,2) and (2,3): 3 of 4 classes TIMEOUT), so a
     TWO-STAGE solver was written (reg2/e5/twostage.py): stage 1 solves the 5-dim line configuration (cached prime components), stage 2 adds
     the genuine element to each component.
 24.2 N TYPE, general system (target 3) -- first chart [exact, reg2/p111/ntype_gen.py, r16_ntype_gen.log].  Keeping ntype1's SUPPORT pattern
     (row lines and R1 vanish in columns 0 and 4) but all values free (charts u0_1 = u3_2 = x_2 = 1, V in echelon form, N modulo R1 by a_2 = 0),
     the level ideal saturated by lam and sum(a) has ONE component, of dimension 1 = the scaling of N: x_2^2 + x_2 + 1 = 0 and everything else
     determined -- i.e. only ntype1 (and its conjugate).  So the 2 extra tangent directions of 23.5 must leave this support pattern (the
     numerical follow-up showed x picking up a column-4 entry); next chart: column-4 entries free (running at the end of the round).
 24.3 two-stage solver test: stage 1 (line configurations) works (cached components, reg2/e5/cache); stage 2 (genuine element on a non-linear
     component, ~30 variables) TIMEOUTs at 60 s for (2,1|2)+R1 on the line-free rows -- stage 2 needs the linear conditions on G (P_2 mixed:
     <x+y,u> = 0 for lines in other rows, <y,u> / <x,u> for lines in rows r / j, x_c v_r + y_c v_j = 0 for column elements, sums) solved
     first over the component, and only then the higher equations.  Not done this round.
STATUS 05:15: resumed round 16 after the usage-limit cut (chart-2 line leftovers of 2121Vni / 2211BD row 0->1; q_rank_exact already fixed).
 24.4 THE TWO OPEN FAMILIES OF 21.4 ARE CLOSED [exact].
     2121Vni row 0 -> 1 (pool omega_e0, r13_oe0_defospan_big.log): E_0-test UNIT on 3 pivot sets; Omega <= <1, e_4> except on the chart-1
       degeneracy line u1+2u2+1 = 0; the pivot sets cover everything except t = 0 points (undeformed) and that line.  On the line, chart 2
       (FAMS '2121Vni_b2_line', u1 = -1-2u2): two independent 16x16 minor sets (r16_2121Vni_b2_line*.log) leave u2 = -1 (the point (1,-1),
       chart 3: t = 0 only, round 13), t = 0 points, and the two conjugate points u2 = -(3 +- 2 sqrt(-3))/7 over Q(w); at those u2 the
       fixed-u2 runs (FAMS '2121Vni_b2_line_w', fix u2 in Q(w)) give 16x16 AND 15x15 minors UNIT for all t (r16_2121Vni_cpoints.log).
       => dim T_1 <= 9 for every t != 0 => FO2 <= 8.
     2211BD row 0 -> 1 (pool omega_e0): E_0 UNIT; the Omega-bigger locus lies in V(f1, f2) for two generators f1, f2 of the printed elimination
       ideal = the chart-1 line v1+2v2+1 = 0 and the points (1,-3), (-1,-1), (-1,1), (1,1) (r16_2211BD_f1f2.log); uncovered pivot points
       (1, -1 +- i sqrt 2) x t.  certify_defo at the 4 points: (1,-3), (1,1): dim T_1 <= 10, gcd of principal 3x3 minors c t^2 (rank q >= 3 for
       t != 0); (-1,+-1): dim T_1 <= 9 for t != 0; (1, -1 +- i sqrt 2): t = 0 only (r16_2211BD_points.log).  Chart 2 on the line (FAMS
       '2211BD_b2_line'): two minor sets leave v2 = -1 (chart-3 point, t = 0 only), t = 0 points and the base points (-1/3,-1/3), (-3,1):
       certify_defo there: dim T_1 <= 10 and gcd = 829440 resp. c t^2 => rank q >= 3 (t != 0).  => FO2 <= 8.
     (omega_e0 prints only the first 200 characters of the Omega-test ideal; the conclusion uses only generators visible in that prefix,
     which is legitimate: their common zero set contains the true locus.)  The pool minors fallback timed out (1700 s) and is not needed.
STATUS 05:19: 2121Vni row 0->1 and 2211BD row 0->1 CLOSED; R3 cone runs in the pool.
 24.5 R3 CASE (I) at a rational point [exact, pool, r13_r3_cone_big.log; script reg2/r3/r3_cone_I_1.sing, n = (1,2,3,-6,0), B of rank 3 from
     the 4-dim B-space]: the admissible cone V_B (15 Z-coordinates) has dimension 3 and consists of 5 prime components, each of dimension 3 and
     degree 2.  An irreducible variety of dimension 3 and degree >= 2 cannot contain a 3-dim linear space (it would coincide with it), and a
     linear space inside a finite union of irreducible varieties lies in one of them => no 6-dim level M of case (I) at this point.  (The same
     one-line argument also covers case (II), 20.1.)  Case (alpha): running in the pool.  General parameters: open (generic computations).
     [CORRECTED round 18 (26.4): MIS-ATTRIBUTED.  The queued chain ran r3_cone_I_1.sing first and it printed 'halt 1' (not finished at the
     cap); the 'cone dim 3 / 5 components of dim 3, degree 2, 9 linear forms' lines come from the SECOND script r3_cone_alpha_1.sing.  Check:
     the alpha ring has 13 variables, case (I) 14; an irreducible cone of dim 3 and degree 2 spans a 4-dim linear space, so 9 independent
     linear forms force 13 variables.  So the argument above closes case (ALPHA) at its rational point n = (1,2,3,4,-10); case (I) is OPEN.]
STATUS 05:42: round 16 report; own background job: twostage test on the ext_10 type (ends by 06:00); pool: R3 cone (alpha) running.
STATUS 05:43: round 17 started (stage-1 sweep of all e=5 classes; linearised stage 2; first cutting lemma; R3 alpha; N type).

## 25. Round 17
 25.1 e = 5 SOLVER, STAGE 1 OVER ALL TYPES [exact, reg2/e5/twostage.py with STAGE1_ONLY; log r17_e5_stage1.log; per-class Singular <= 60 s,
     <= 0.5 GB].  Stage 1 = the 5-dim LINE configuration of the type's pattern and incidence class (all level equations of the five line elements,
     saturated by the part ranks), decomposed into prime components (cached, reg2/e5/cache).  Over the 296 types / 1370 classes:
       66 types killed by orthogonality of the line parts (P2); 214 classes killed by incidence (P1);
       452 classes LINES-EMPTY (no 5-dim level line configuration at all)  -- the stage-1 kill;
       74 classes TIMEOUT in stage 1 (60 s);  630 classes have line components (24 of them only linear components, 606 non-linear).
     36 types lose all their classes in stage 1.  So stage 1 cuts the 1156 pre-check survivors to 630 (+74 open).
 25.2 STAGE 2 LINEARISED.  The level equations have degree <= 2 in the genuine element G (a two-row/two-column element enters a k-row term at most
     twice), so stage 2 splits into the LINEAR system L(lines) g = 0 (P_2-mixed and all degree-1 terms, + sums) and quadratic conditions.
     (a) exact, all-in-one: the linear part alone still TIMEOUTs (120 s) for 2 of the 3 non-trivial classes of (2,1|2)+R1 on rows (2,3)
         (twostage.py LINEAR_ONLY); the third is LINEAR-NONEMPTY;
     (b) numerical generic rank (reg2/e5/stage2n.py, a MEASURE): at a random point of each line component the linear system has kernel 0
         for all 3 classes ("LINEAR-GENERIC-KILL") -- yet ext_10 is a member of this type: the members live on the RANK-DROP sublocus of the
         line component.  So the exact stage 2 must compute that sublocus (maximal minors / Fitting ideal of L over the component) and solve
         there; the linear conditions are strong (they reduce to a proper subvariety) but do not kill by themselves.  Sweep over all types:
         r17_e5_stage2n.log (running at the end of the round).
 25.3 STAGE-2 LINEAR MEASURE over all types [numerical, reg2/e5/stage2n.py, r17_e5_stage2n.log].  For each of the 630 classes with line
     components, the kernel of the linear system in G at a random point of each component, MINUS the gauge directions (G -> G + line element
     of the rows (columns) of the genuine pair: dim = a_r + a_j resp. b_c + b_d):
       366 classes: genuine kernel 0 on every component ("LINEAR-GENERIC-KILL") -> members can only lie on the RANK-DROP subloci of the line
            components (example: ext_10 lies on such a sublocus of its (2,1|2) configuration);
       264 classes: genuine kernel >= 1 on some component (339 components with kernel 1, 34 with 2, 5 with 3) -> the quadratic conditions decide;
       74 classes: stage 1 still open (TIMEOUT 60 s).
     Survivors by genuine type: N-type pairs dominate (about 178 of the 264), R1/C1 about 86; an R1 element on two LINE-FREE rows survives in
     only 1 class.  So the most valuable cutting lemma is one about N elements, then R1 on rows with lines.
 25.4 Symmetry: classes are orbit-reduced under the full stabiliser of the TYPE inside S_4 x S_5 (row/column permutations preserving the
     part dimensions and the genuine pair); stage-1 work is shared across types through the cache: the 1370 (type, class) pairs involve at
     most 200 distinct (pattern, incidence class) line configurations (97 with components, 63 empty, 31 P1, 9 timeouts).
 25.5 Pool results.  (3|3) row 0 -> k with free S: the 33_S_row1 minors leave 5 S-directions; along each, 16x16 minors are UNIT or leave only
     t = 0 (r17_33row_directions.log) => CLOSED [exact] (rows 0 -> 2, 3 by the S_3 symmetry of rows 1..3).  (3,1|2) along S ~ (1,1,1):
     pool run leaves base points (0,-1), (0,0) [t = 0 only, r17_312_points.log], (0, w), (0, w^2) [the deformation is TRIVIAL there: rank B = 1,
     M(t) = M(0), a (3,1|2) member] and further components cut off in the pool log; a full rerun is running (r17_rank_312_d3_1_full.log).
     R3 case (alpha): the pool cone run was still running at the end of the round.
 25.6 Rank-drop restriction (exact) attempted: two-sided random combinations det(R L C) of the (n_g - gauge)-minors (in the minor ideal by
     Cauchy-Binet) added to the component -- the 10x10 determinant with polynomial entries exhausts 0.5 GB ("no more memory", ext_10 type).
     Next: evaluate on a rational parametrisation of the component (when it has one) or use a block elimination order with the line variables
     as parameters; or compute the Fitting ideal only on the 366 LINEAR-GENERIC-KILL classes, in the big slot.
STATUS 06:16: round 17 report; own background job: 312_d3_1 full rerun (<= 0.5 GB, ends by 06:40).
STATUS 06:16: round 18 started (N-element cutting lemma; rank-drop loci per configuration + big-slot batch; stage-1 timeouts; (3,1|2), R3 alpha).
STATUS 06:42: numerical QUADRATIC stage (stage2q.py) written; first sweep invalid (kernel basis conj bug, gauge too small) -> fixed, sweep rerunning (r18_e5_quad.log); REG2-E5-BATCH queued (coordinator: REG2E5BATCH after verifyfl's P1 batch).

## 26. Round 18
 26.1 NUMERICAL QUADRATIC STAGE for all e = 5 classes [numerical MEASURE, not a proof; reg2/e5/stage2q.py, driver all_types_e5_stage2q.py,
     log r18_e5_quad.log (one CLASS line per class with per-component verdicts)].  At a random point of every cached stage-1 component:
     (i) the linear system in G (all equations of G-degree <= 1, + sums for R1/C1); (ii) the GAUGE = row lines on the pair P, Q plus ALL
     combinations of cross lines supported on P, Q only (e.g. a(e_P - e_Q) (x) e_c from column lines); (iii) the genuine kernel K = ker mod
     gauge; (iv) the equations of G-degree 2 on K, solved from 16 random starts (chart s = sum x = 1 for N); each solution is classified
     'one' (single row/column matrix mod gauge => e = 6, not this type), 'line' (x or y in the gauge span), 'gen' (genuine; also tested for
     rank one mod gauge).  Every level equation of M = Lin (+) <G> has G-degree <= 2 (G lives on two lines), so (i)+(iv) is the complete system.
     RESULT: NO class has a genuine solution at a generic point of any component.  Of the 630 classes with components:
        linear stage kills (genuine kernel = gauge, or s = 0 forced for N):  C1 125, R1 102, N 260 (181 kernel = gauge, 82 with s = 0 forced)
        quadratic stage kills (genuine kernel != 0, no genuine quadric solution):  C1 31, R1 57, N 55            -> 487 + 143 = 630.
     So members of e = 5 types can only sit on PROPER closed subsets of the components (rank-drop loci of the linear system mod gauge, or
     the loci where the quadratic system acquires a genuine solution).  The round-17 measure "264 classes with a free direction" counted
     gauge directions (it subtracted only a_P + a_Q, not the cross-line combinations) -- superseded by this table.
     Two bugs were found and fixed during the round (renamed logs r18_e5_quad_BUGGY_conj.log, r18_e5_quad_PARTIAL_superseded.log): the
     kernel basis after the gauge projection was conjugated (left the kernel: the 'survivors' were not level, level error ~10), and the cross
     gauge only used single cross lines (a 6-dim 'survivor' of 1100|21000 row(0,1) N was line-spanned: srow [2,1,0,0], scol [2,1,0,0,0]).
 26.2 N ELEMENTS (target 1).  Notation G = e_P x + e_Q y, s = sum x = -sum y != 0, <x,y> = -s^2 (P_2), z = x + y.
     LEMMA N0 [rigorous, two lines]: the only elements of Lin(M) supported on the lines P, Q with nonzero row sum are sum_c a_c (e_P - e_Q) (x) e_c
     (row lines have sum 0).  If Lin(M) contains one (e.g. a FREE COLUMN, b_c = 3, or a 2-dim column part W_c containing e_P - e_Q), then
     G - (s / sum a_c) * that element is a sum-zero (R1) element congruent to G mod Lin(M): the N type of that pattern is covered by the R1 type.
     Cuts at once: the 5 row-kind N classes with components and b_c = 3; on every other class the cross-gauge locus.
     LEMMA N1 [rigorous]: a column line v e_c gives (P_2 mixed) s (v_Q - v_P) + v_P x_c + v_Q y_c = 0 and (P_3) (v_P + v_Q)(s (x_c - y_c) + 2 x_c y_c) = 0;
     two column lines in column c with independent (v_P, v_Q) force (x_c, y_c) = (s, -s) (G looks like s (e_P - e_Q) (x) e_c in column c), and
     then the P_3 condition is automatic.  A row line u on a third line k gives <z,u> = 0 and s <x,u> + sum_a x_a y_a u_a = 0; on line P: <y,u> = 0.
     ntype1 (e = 4) is RANK ONE: y = -x there (x = (0, w+2, 1-w, 0, -1), sum x = 2, <x,x> = 4 = s^2), the N analogue of "R1 => rank one".
     NOT obtained: a support statement of the form "N forces two line elements on its rows" -- the data give no such pattern (everything dies
     at generic points anyway; the linear stage alone forces s = 0 in 82 N classes, i.e. there N degenerates to R1).
 26.3 twostage.py GENUINENESS FIX (matters for REG2-E5-BATCH, which calls twostage.py at run time; queue line unchanged; old version kept as
     reg2/e5/twostage_r17_backup.py).  For R1/C1 the old saturation by (gx), (gy) let G = (row line on P) + (row line on Q) in Lin(M) pass,
     so EVERY R1/C1 class with lines on both lines P, Q came out NONEMPTY.  Now: saturate by the maximal minors of [U_P; x] and of [U_Q; y]
     (x not in U_P, y not in U_Q; for a = 0 the entries, as before).  Old EMPTY verdicts stay valid (old saturation was weaker).  Test
     (r18_twostage_gaugefix_test.log): 1100|21000 row(0,1) R1: old NONEMPTY dim 12, NONEMPTY dim 13, TIMEOUT x2; new NONEMPTY dim 12, TIMEOUT x3.
     A NONEMPTY verdict is still not a member: it can be an N element with cross gauge (Lemma N0) or an e = 6 degeneration (Lin jumps on a
     special locus); NONEMPTY classes need a point + invariants (next step).  EMPTY is final.
     BIG SLOT: REG2-E5-BATCH (batch_e5.py, resumable, one verdict line per type, RETRY_TIMEOUTS for the 74 stage-1 timeouts) is queued by
     the coordinator as REG2E5BATCH (2.5 GB, 3 h) + LOW_REG2E5BATCH2 (6 h continuation).
 26.4 R3 CORRECTION + case (alpha).  r13_r3_cone_big.log: the chain ran r3_cone_I_1.sing FIRST and it printed 'halt 1'; the lines 'cone dim 3,
     5 components of dim 3, degree 2, 9 linear forms' are from r3_cone_alpha_1.sing (ring sizes 14 vs 13; an irreducible dim-3 degree-2 cone
     spans a 4-dim linear space, so 9 independent linear forms need 13 variables).  Hence [exact] case (ALPHA) at the rational point
     n = (1,2,3,4,-10) (B as in the script) has no 6-dim level M (cone argument); case (I) is OPEN (24.5 / R16-5 flagged in place).
 26.5 (3,1|2) along S ~ (1,1,1) [exact unless marked; r17_rank_312_d3_1_full.log, r17_312_points.log].  The 15 components of the full rerun:
     7 lie in t = 0 (undeformed (3,1|2) members); base points (0,-1), (0,0), (-1,0), (-2,0): fixed-point runs leave only t = 0 => dim T_1 <= 9
     for t != 0; (1,-3): UNIT; (0, w), (0, w^2) [round 17] and (w^2, w), (w, 0) (+ conjugates): the deformation is TRIVIAL (rank B = 1,
     rank [M0; M] = 6: M(t) = M(0) is a (3,1|2) member with (dim T_1, rank q, FO2) = (10, 4, 8)) [numerical, defo3_num.py].  So (3,1|2) along
     (1,1,1) is CLOSED except that the triviality at the four w-points is numerical (exact check over Q(w) = next).
STATUS 06:55: quadratic measure done (no generic survivor among 630 classes); Lemma N0/N1; twostage genuineness fixed before the batch; R3 attribution corrected (alpha closed at its point, (I) open); (3,1|2) leftover points certified.
 26.6 GENERIC KILLS ARE NOT ENOUGH -- e = 5 MEMBERS EXIST ON SPECIAL LOCI (important for reading 26.1).  The census spaces ext_9, ext_10,
     ext_11 (level 1e-12; srow [0,2,0,1], scol [0,0,2,0,0], i.e. type 2100|20000 with R1 on the two line-free rows), dr35_u2_s52_400
     (2200|10000) and dr35_u3_s41_116 / _29 (3100|10000) are genuine e = 5 spaces (same part dimensions at tol 1e-7 and 1e-4); their R1
     element is RANK ONE (y = -x, isotropic), and their classes are 'Q0' (linear kill) in 26.1 -- so they sit on the rank-drop locus.
     GLOBAL numerical solver reg2/e5/stage2g.py (line parameters AND G as unknowns: component + all level equations + per-line charts +
     bilinear gauge fixing with Rabinowitsch variables for the Gram determinants and for line independence; every converged point is checked:
     level error, rank 6, single-row/column part dimensions).  Without an ansatz, Gauss-Newton is pulled to the e = 6 degenerations and does
     NOT find the ext_10 members (2100|20000 row(2,3) R1, 24 starts per class: only e6 / inLin / nonlevel).  With the RANK-ONE ansatz y = -x
     (RANK1=1) it finds them: class 00, 4 of 16 starts give genuine e = 5 members, srow [2,1,0,0], scol [2,0,0,0,0], level 1e-13,
     (dim T_1, rank q, FO2) = (9, 3, 7) like ext_10 (r18_global_rank1_validation_inv.log).  Every known genuine element of an e <= 5 space
     is rank one: the R1 elements of ext_*, dr35_* and the N element of ntype1.
     RUNNING (own jobs, <= 0.5 GB each, 1 core each, ~1-2 h): r18_e5_global.log (no ansatz) and r18_e5_global_rank1.log (rank-one ansatz),
     one GCLASS line per class (gen5 / e6 / inLin / nonlevel / fail counts); genuine points dumped to reg2/e5/dumpg/ (then inv_dump.py).
     CANDIDATE LEMMA (would collapse stage 2): "a genuine two-line element of an e = 5 space is rank one mod Lin(M): G = (e_P - e_Q) (x) x,
     with sum x = 0, <x,x> = 0 (R1) or <x,x> = (sum x)^2 (N)".  Not proved; the generic-point data of 26.1 are consistent with it (the
     non-rank-one directions die everywhere at generic points), and with it the exact stage 2 has 5 instead of 10 G-unknowns.
STATUS 07:04: e = 5 members exist on special loci (census ext_*/dr35_*; rank-one global solver finds them, FO2 7); two global sweeps running (own, <= 0.5 GB).
STATUS 07:08: round 18 report (NOTES 26, RESULT ROUND 18); own background jobs: r18_e5_global.log and r18_e5_global_rank1.log (<= 0.5 GB each, timeout 2 h).
STATUS 07:09: round 19 started (rank-one lemma; exact rank-one split in twostage; FO2 of known e=5 members; R3 (I); w-point triviality).

## 27. Round 19
 27.0 Formulas used below were re-derived by inclusion-exclusion and CHECKED by brute force on random data (reg2/e5/check_mixed.py,
     r19_check_mixed.log).  Row kind: G = e_P (x) x + e_Q (x) y, s = sum x, sum y = -s, z = x + y, <a,b> = sum a_i b_i, V = 1^perp in C^5;
     U_k = row-line space of row k, U' = sum of U_k over the two rows k != P, Q; W_c = column-line space of column c (in C^4).
       P_2(G) = -(s^2 + <x,y>);  P_2(G, e_k u) = -<z,u> (k != P,Q);  P_2(G, e_P u) = -<y,u>;  P_2(G, v e_c) = s(v_Q - v_P) + x_c v_P + y_c v_Q;
       P_3(G, e_k u, e_l w) = 2 sum z u w  (u, w in different other rows);  P_3(G,G,e_k u)/2 = s<x,u> - s<y,u> + 2 sum x y u;
       P_3(G, e_k u, v e_c) = (v_P + v_k)<x,u> + (v_Q + v_k)<y,u>  when u_c = 0;
       P_3(G,G,v e_c)/2 = -(v_P + v_Q)(s(x_c - y_c) + 2 x_c y_c - (s^2 + <x,y>)).
     All mixed P_k forms are sums over distinct rows and distinct columns, hence invariant under transposition: every statement below holds
     for COLUMN kind with rows <-> columns, C^5 -> C^4 (V = 1^perp in C^4, sum of 1 = 4).
 27.1 RANK-ONE LEMMA, PARTIAL [rigorous].  Let G be a genuine two-row element (R1 or N) on rows P, Q.  "Rank one mod Lin(M)" means
     z in U_P + U_Q (then G - e_P u - e_Q u' = (e_P - e_Q) (x) x' for suitable u in U_P, u' in U_Q).
     (1) z in V cap U'^perp  (P_1 and P_2(G, e_k u)).
     (2) If dim U' = 4 (U' = V) then z = 0: V cap V^perp = V cap C1 = 0 because sum 1 = 5 != 0.        [column kind: dim W' = 3]
     (3) If dim U' = 3, U' = V cap mbar^perp with mbar in V (unique up to scale), then z = gamma mbar, and gamma = 0 as soon as
         (3a) some u in U_k, w in U_l (the two other rows) have sum_a mbar_a u_a w_a != 0   [P_3(G, e_k u, e_l w) = 2 gamma sum mbar u w], or
         (3b) some column line v e_c has v_P = v_Q != 0 and mbar_c != 0   [P_2(G, v e_c) = v_P z_c for v_P = v_Q, for R1 AND N].
     (4) [R1] If U' = H_c := {w : w_c = 0, sum w = 0} (mbar ~ 5 e_c - 1) and some column line v e_c has v_P != v_Q, then M has NO R1 element on
         P, Q: P_3(G, e_k u, v e_c) with u_c = 0 and <y,u> = -<x,u> gives (v_P - v_Q)<x,u> = 0, so x, y in U'^perp = span(e_c, 1); sum 0 gives
         x = b (1 - 5 e_c), y = b' (1 - 5 e_c), and <x,y> = 20 b b' = 0 forces x = 0 or y = 0 (not genuine).  [column kind: 12 b b']
     (5) [R1, U' = H_c] combining (3b) and (4): an R1 element exists only if every column line in column c has v_P = v_Q, and then it is rank one
         (z = 0) unless all of them vanish on P and Q.
     APPLICATION: type 2100|20000 R1 on the two line-free rows, incidence class 00 (row lines vanish in the column of the two column lines,
     so U' is in H_0): off the locus dim U' <= 2, every R1 member has W_0 = {v in V_4 : v_P = v_Q} and is RANK ONE -- exactly the structure
     of ext_9..11 (r19_census_anatomy.log: z = 0, s = 0, <x,x> = 0, both column lines with v_P = v_Q, U' = H_2 in their coordinates).
     All six census members have dim U' = 3, z = 0 and v_P = v_Q for every cross line (r19_census_anatomy.log).
     OPEN: dim U' <= 2; U' = V cap mbar^perp with mbar not of the form 5e_c - 1 and (3a), (3b) both failing; the N analogue of (4) (there
     x, y in span(e_c, 1) with b v_P + b' v_Q = 0 on W_c -- not yet excluded).
STATUS 07:28: rank-one lemma partial (27.1) written; split test rerunning with TMO 400.
 27.3 EVERY KNOWN GENUINE e = 5 MEMBER HAS FO2 <= 8 [numerical; reg2/e5/inv_dump.py, r19_census_e5_inv.log, r18_global_rank1_validation_inv.log].
     Leaf 10 for e = 5 is therefore "every e = 5 member has FO2 <= 8", NOT "no e = 5 member exists":
        space                         type (canonical)         genuine element            (dim T_1, rank q, FO2)
        ext_9, ext_10, ext_11         2100|20000 R1, free pair  rank one, isotropic       (9, 3, 7)
        dr35_u2_s52_400               2200|10000 R1, free pair  rank one, isotropic       (9, 3, 7)
        dr35_u3_s41_116, _29          3100|10000 R1, free pair  rank one, isotropic       (10, 4, 8)   <- at the bound
        stage2g rank-one points (4)   2100|20000 R1, class 00   rank one                  (9, 3, 7)
     (level errors 1e-12 .. 1e-13; e = 5 checked with the part dimensions srow/scol at tol 1e-7 and 1e-4.)  dr35_u3_* reach FO2 = 8 exactly,
     so the 3100|10000 family needs an exact rank q >= 4 wherever dim T_1 = 10 (or dim T_1 <= 9 elsewhere) -- a target for the exact pass.
 27.4 (3,1|2) along S ~ (1,1,1): EXACT triviality at the w-points [reg2/gb/defo_trivial_exact.py, r19_312_wpoints_exact.log]: the deformation
     is M0 + t D (linear in t); over QQ<sqrt(-3)> rank [M0; D] = 6 = rank M0 at (m1,m2) = (w^2, w), (w, 0), (0, w) => M(t) = M(0), a (3,1|2)
     member (TRIVIAL); the conjugate points follow by Galois conjugation (the family is defined over Q).  Calibration: (1,-3) gives rank 8
     (GENUINE), as numerically.  With 26.5: (3,1|2) along (1,1,1) is CLOSED [exact].
     (4') [R1 AND N] If U' = H_c and the restriction W_c -> C^{P,Q}, v -> (v_P, v_Q), is ONTO, there is no genuine two-row element on P, Q.
         Proof: as in (4), x, y in span(e_c, 1): x = a e_c + b 1, y = a' e_c + b' 1 (a + 5b = s, a' + 5b' = -s); then
         P_2(G, v e_c) = s(v_Q - v_P) + x_c v_P + y_c v_Q = -4 (b v_P + b' v_Q), so b = b' = 0 and G = a (e_P - e_Q) (x) e_c is a single-column
         matrix (e >= 6), not a genuine e = 5 element.  If the restriction has rank 1, spanned by (p, q) with p != q, then (b, b') ~ (q, -p)
         and N is not excluded by this argument (R1 is, by (4)).
     (Checks for (4'): P_3(G,G,e_k u), P_3(G, e_k u, e_l w) and P_4(G,G,e_k u, e_l w) are identically 0 for x, y in span(e_c, 1), u, w in H_c,
     so no further information comes from the other rows.)
 27.5 R3 CONE ARGUMENT -- GAP FOUND AND (PARTLY) CLOSED.  20.1 / 24.5 / 26.4 used "a prime component of dim 3 and degree 2 contains no 3-dim
     linear space".  minAssGTZ over Q returns Q-IRREDUCIBLE components; a degree-2 component could be two Galois-conjugate 3-planes (a quadric
     of rank 2 in its 4-dim span), which DOES contain 3-dim linear spaces (over a quadratic field).  The correct criterion: the component's
     quadric (the single degree-2 element of its reduced GB, reduced against the linear forms) has Hessian rank >= 3 -- then it is irreducible
     over C.  Checked [exact, Singular over Q; copies r3/r19_*_rank.sing]:
        case (II), B = (2,1,3,-1):  6 components, each one quadric of Hessian rank 3  (r19_caseII_B2_rank.log)  => argument VALID;
        case (II), B = (1,-2,5,3):  6 components, each one quadric of Hessian rank 3  (r19_caseII_B1_rank.log)  => argument VALID;
        case (alpha), n = (1,2,3,4,-10): rerun with the rank print in progress (r19_alpha_rank.log) -- until then 26.4's "(alpha) closed at its
        point" is CONDITIONAL on Hessian rank >= 3.
STATUS 07:44: R3 cone argument needs absolute irreducibility; case (II) both B verified (Hessian rank 3); alpha rerun running; DROPU test running.
        case (alpha): 5 components, each one quadric of Hessian rank 3 (r19_alpha_rank.log; this rerun fit in 0.5 GB)  => argument VALID:
        R3 (alpha) at n = (1,2,3,4,-10) is closed [exact].
     Case (I): modular run r3/r19_r3_cone_I_1_modp.sing (p = 32003).  Rigorous because the ideal is homogeneous with integer generators:
     HF of the mod-p ideal >= HF over Q, so dim_p >= dim_0; and a 3-dim linear subspace of V_B over Qbar reduces (saturated lattice) to a 3-dim
     linear subspace of V(I_p) over Fpbar.  So "dim_p <= 2", or "every top-dim mod-p component is a quadric cone of Hessian rank >= 3 in a
     4-dim span" (p odd), excludes it.
 27.6 R3 CASE (I) at n = (1,2,3,-6,0), seed-1 B (the 24.5 point) [exact + modular; r3/r19_r3_cone_I_1_modp*.sing, r19_caseI_lift.py,
     r19_caseI_spaces.py; logs r19_caseI_modp.log, r19_caseI_modp2.log, r19_caseI_modp_linear.log, r19_caseI_lift.log, r19_caseI_spaces.log].
     Mod 32003 the ideal is homogeneous, dim_p = 3, and the top-dim components are FIVE LINEAR 3-spaces and five quadric cones of Hessian rank
     3 (plus dim-2 components); the same at p = 31991.  The five linear spaces lift to Q (rational reconstruction) and lie in V_B EXACTLY
     (reduce(I, std(L)) = 0 over Q for all five).  So the plain cone argument FAILS for case (I) -- V_B does contain 3-dim linear spaces.
     But each of the five gives M = P_0 + N with N spanned by LINE elements ((e_1 - e_2) (x) e_c, the row-0 line (-1,-2,-3,6,0)/6 and a
     column-4 line): M is a 6-dim level space (level error 1e-13), e = dim Lin(M) = 4, and the 3-dim row block P_0 has rank 2 MODULO Lin(M)
     (one direction of P_0 becomes a single-row element of row 3: Bw_0 is proportional to the row-0 line).  So these are NOT R3 spaces (e = 4,
     2-dim genuine part) and have (dim T_1, rank q, FO2) = (9, 3, 7) [numerical].
     Conclusion at this point: any 6-dim level M of case (I) gives a 3-dim linear L in V_B; L reduces mod p into a top-dim component of
     V(I_p), hence (the quadric components being absolutely irreducible and nonlinear) onto one of the five linear spaces.  The five
     Q-rational ones are non-R3 with FO2 = 7.  Remaining gap: another Qbar-subspace with the SAME reduction (excluded if the mod-p Fano
     scheme is reduced at the five points; two primes give the identical picture).  R3 (I) at general parameters: open.
     LESSON for leaf 11: the R3 cones can contain degenerate linear spaces (blocks whose rank drops modulo Lin); the cone test must be read
     as "every 3-dim linear subspace is degenerate", not "none exists".
STATUS 07:52: R3 (I) at its point: five linear 3-spaces in V_B, all degenerate (P_0 rank 2 mod Lin, FO2 7); rank-one sweep resumed.
STATUS 07:53: RESULT ROUND 19 written.
 27.7 RANK-ONE LEMMA, second part [rigorous].
     LEMMA ISO: if t in V (sum 0) is isotropic and nonzero, then t o t (Hadamard square) is NOT in span(1, t).  Proof: t_a^2 = l + m t_a for all a
     means t takes <= 2 values a (k times), b (n-k times); k a + (n-k) b = 0 and k a^2 + (n-k) b^2 = 0 give (n-k) b^2 n / k = 0, so t = 0
     (n = 5 rows kind, n = 4 columns kind; k in {0, n} gives t = n a / n = 0 directly).
     LEMMA INT: if dim U' = n - 2 (3 for rows) and U_k cap U_l != 0 for the two other rows, then z = 0.  Proof: 0 != t in U_k cap U_l is
     isotropic (U_k perp U_l) and orthogonal to U' = U_k + U_l, so mbar ~ t and z = gamma t (27.1(3)); P_3(G, e_k t, e_l w) and
     P_3(G, e_k u, e_l t) give gamma <t o t, w> = gamma <t o t, u> = 0 for all u in U_k, w in U_l, so gamma != 0 would put t o t in
     U'^perp = span(1, t), contradicting ISO.  [column kind: two of the three other columns, W' 2-dim]
     CONSEQUENCES (G any genuine two-line element, R1 or N; z = 0 EXACTLY, everywhere on the type):
       rows, other two rows carry (3,1) lines:  U_k = V cap mbar^perp, U_l = <u>, u ~ mbar; dim U' = 4 (z = 0 by (2)) or u isotropic, u in U_k
            (LEMMA INT)  =>  ALWAYS rank one.   [type 3100|10000 on the free pair = the dr35_u3 family; 6 classes with components]
       rows, (2,2):  dim U' = 4, or U_k cap U_l = <t> (INT)  =>  rank one unless U_k = U_l is a totally isotropic plane.  [2200|10000 = dr35_u2
            family, whose members sit exactly on the INT locus; 4 classes]
       columns, other three columns carry (3,0,0) (free column; also PFC), (2,1,0) [W_f' in W_f or dim 3] => ALWAYS rank one; (1,1,1) => rank
            one unless the three column lines are proportional (three pairwise orthogonal lines spanning a plane in V_4 must have two equal:
            a totally isotropic plane does not exist in the 3-dim nondegenerate V_4).   [4 + 14 + 14 classes]
     So 42 of the 630 classes are rank one outside explicit small loci (U_k = U_l isotropic plane; three proportional column lines).  Open:
     other rows (3,0), (2,1) [partly 27.1(4)-(5)], (2,0), (1,1), (1,0), (0,0) and the column analogues -- there the parallel lines on the other
     lines span <= 3 dims with trivial pairwise intersections, and the rank-one statement must come from the cross lines (27.1(3b),(4)).
STATUS 07:54: rank-one lemma part 2 (ISO, INT): (3,1), (2,2), column (2,1,0), (1,1,1) patterns rank one.
STATUS 07:55: round 19 report; own background job: r18_e5_global_rank1.log (rank-one global sweep, <= 0.5 GB, ends by ~09:00 via timeout).
STATUS 07:57: round 20 started (3100|10000 family at the bound; other census families; rank one for (2,1)/(3,0); R3 (I) gap).

## 28. Round 20 (aborted by Kevin at ~08:02 UTC)
 28.1 THE 3100|10000 R1 FAMILY IS ONE RIGID SPACE, FO2 = 8 EXACTLY [rigorous derivation + exact computation].
     Type: row r0 with three lines U_0, row r1 with one line u, column c with one column line v, R1 element on the two line-free rows P, Q.
     Derivation (formulas of 27.0; E4 = 4-fold distinct sum = <x,x><w,u> + 2<x,w><x,u> - 6 sum x^2 w u by Moebius over set partitions):
       G = (e_P - e_Q) (x) x (27.7, (3,1) case); U_0 = V cap u^perp; P_3(G,G,e_k w) gives x o x perp U_0 + <u>, so u is isotropic (else
       x o x in C1, impossible with sum x = 0) and x o x in span(1,u); v_{r0} = 0 (else U_0 = H_c, u ~ 5e_c - 1 not isotropic); x_c = 0
       (else v_P = v_Q and v_P + v_Q = 0, v = 0); P_3(G, e_{r0} w, v e_c) = (v_P - v_Q)<x,w> forces v_P = v_Q (else x ~ u, then u o u in
       span(1,u), contradicting ISO), so v ~ (0,-2,1,1) and u_c = 0; hence x o x = mu u (lambda = 0 at coordinate c), mu != 0, u = x o x;
       P_4(G,G,e_{r0} w, e_{r1} u) gives p3 x - 3 x^4 in span(x^2) (coordinatewise), so the nonzero x_a are roots of 3t^3 + b t - p3 and
       p3(1 - N/3) = 0 (N = number of nonzero entries); N = 3 with p1 = p2 = 0 gives x = r(1,w,w^2) on a 3-set S not containing c; p3 = 0
       would give p1..p4 = 0 and x = 0.  So up to permutations, Galois conjugation and scaling the type has exactly ONE member:
         c3100 = { U_0 = V cap u^perp in row 0, u = (1,w,w^2,0,0) in row 1, v = (0,-2,1,1) in column 3, G = (e_2 - e_3) (x) (1,w^2,w,0,0) }.
     Exact (reg2/gb gen_rank.py FAMS 'c3100', reg2/c3100/levelcheck.py, q_rank_exact.py; log r20_c3100_exact.log): level (all level
     polynomials 0 mod w^2+w+1), dim T_1 = 10, rank q_Y = 4 (two Y; 3 for a special Y) => FO2 = 10 - 2 = 8 <= 8.  Rigid, so no jump of
     dim T_1 within the type.  Numerically (stage2g RANK1, 24 starts) all 11 genuine points found are this space (reg2/c3100/c3100_num.py).
     NOT done: the N element on the same pair (run stopped by the abort), the other pairs of pattern 3100|10000 (batch classes), deformations
     out of the type (they belong to other types).
 28.2 OPEN at the abort: 2100|20000 / 2200|10000 census families exact (target 2); rank one for (2,1)/(3,0) other-row patterns (target 3);
     R3 (I) second-lift / Fano gap and generic parameters (target 4); REG2E5BATCH / LOW_REG2E5SPLIT queued but not run by me.
STATUS 08:04: STOPPED 08:04 UTC (L-gct-210 aborted by Kevin; no own jobs running; handover/HANDOVER-reg2.md written).
