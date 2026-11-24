# NOTES-lowd (role: lowd; start 12:28, budget 75 min -> ends ~13:43)
## RESULT (13:05) -- d=1 and d=2 NOT proved. What is settled:
 (R1) [exact, trivial] For the GAP the d-case only needs  r <= 8 - d  (dim L = r + d, r = dim pi(L) <= 8).
      So d=1 needs only "r != 8" (pi(L) != V(+)V), NOT (S)'s "alpha-, beta-projections not both onto".
      "r <= 7 for every level L" (true if max dim is 7) would settle d=1 at once.
 (R2) [numerical, robust] r = 8 is impossible already from P_2, P_3 (no g, no P_4, P_5): see below.
      But the minimal infeasible component set has 136 equations in 128 unknowns while every proper
      subset tried is feasible -> looks like plain overdetermination, no visible slick identity.
 (R3) [numerical] (S)'s d=1 case ("not both onto") genuinely needs P_4 (P2,P3 + g-heavy P4 feasible).
 (R4) [exact, new here] Frobenius-Koenig column/row lemma (FK) and consequences (below): for level L and
      each column c there is n_c with sum(n_c)=1 and n_c . x[:,c] = 0 for all x in L (rows likewise);
      if L contains a full one-column space {y e_c^T} then every x in L has column-c sum 0 (r_B <= 3);
      dim L = 9 => every row (column) kills a >= 5-dim subspace, every 2x4/4x2 block a >= 2-dim one,
      every 3x3 block a >= 1-dim one.
 (R5) [exact] column-centred P_2..P_5 formulas (below, verified 1e-13) -- the right coordinates for X_A.
 (R7) [numerical, NEW, possibly the main lead] P_2 = P_3 = 0 ALONE seem to force dim <= 7 at n = 5, for ANY
      subspace of the 24-dim sum-zero space (no level structure, no split needed):
        general chart LM (lowd/p23gen.py): dim 7 found 3/3 (res 1e-13), dim 8 found 0/6 (stall 0.12-0.21);
        seeded at L080 + random vector and at ex.1 (rc45p1) + random vector (p23seed.py): dim 8 0/8;
        2-rows+2-cols support (p23supp.py): dim 7 found 2/3, dim 8 0/4.
      Count: Gr(m,24) has m(24-m) params, P_2,P_3 give C(m+1,2)+C(m+2,3) equations: m=7: 119 vs 112,
      m=8: 128 vs 156, m=9: 135 vs 210.  So the gap would follow from "no 9-dim subspace is totally isotropic
      for P_2 and P_3" -- a quadric+cubic statement; in u-coordinates the forms are
      p_2(u) - (125/9)(p_2 al_u + p_2 be_u) and p_3(u) - (125/9)(p_3 al_u + p_3 be_u).
      Caveat: LM negatives at n=5 can miss special structures (dc5: V(x)v); the r=7 and dim-7 calibrations pass.
 (R6) [numerical counterexample] "column-centred level + alpha onto => contains a one-column space" is FALSE
      (lowd/ccg_81_1.npy, dim 5, d=1, fresh orthonormal residual ~1e-12): contains only 3 dims of the
      column-4 space; DC element g ~ v (x) (1,i,-1,-i,0), v ~ (-1/2,0,-1/2,1,0) (rank one, 4th roots).
      So the obvious classification route to r != 8 fails as stated.
Task: prove case d=1 (then d=2) of the split target (S): min(r_A,r_B) + d <= 4.
STATUS 12:35: started; reading notes, setting up polarization identities.
STATUS 12:52: KEY REFRAMING + numerics (lowd/*.py, LM with fixed damping; "feasible" = res < 1e-10 with
 well-conditioned M / independent basis; "infeasible" = all starts stall at O(1)-O(100)).
 (1) For the GAP the d=1 case only needs  r != 8  (dim L = r + d), i.e. R = pi(L) != V(+)V.  This is much
     weaker than (S)'s d=1 case "not both onto".  And numerically r = 8 is impossible ALREADY FROM P_2, P_3
     (no g, no P_4, P_5 needed):  L >= X_A (+) X_B, X_A = {a (x) 1 + Gamma_A a}, X_B = {1 (x) b + Gamma_B b}
     (Gamma into DC), P_2 = P_3 = 0 on the 8-dim span: 4+3+3 starts all stall (r8lm.py, r8lm2.py).
     Bidegree components (k,j) = coeff of s^j in P_k(s x + y), x in X_A, y in X_B:
       P2 all + P3 cross (31,32): FEASIBLE.  P2 all + P3 pure (30,33): FEASIBLE.
       P2 all + 31 + 33: FEASIBLE.  P2 all + 32 + 33: FEASIBLE.
       P2 all + 31 + 32 + 33: INFEASIBLE.  21,22 + all P3 (no P2-BB): INFEASIBLE.
     So the obstruction needs both cross P3 terms and one pure P3 term.
 (2) (S)'s d=1 case ("A, B not both onto") genuinely needs P_4: d=1, dim 5 graph spaces (g + 4 vectors with
     alpha bijective, beta = M alpha, M invertible) with P2, P3 all + P4 (g-degree >= 2): FEASIBLE; with all
     of P2..P4: INFEASIBLE (drift to singular M).  Without g, 4-dim graph spaces with P2..P4: FEASIBLE;
     with P2..P5: drift to singular M (so conjecturally r_A = r_B = 4 is impossible even for d = 0).
 (3) A-onto level spaces with a DC element found by LM (aonto.py, 4 starts) all have
     g = (e_a - e_b) w^T, w = c(1,0,omega,omega^2,0)-type (e1(w)=e2(w)=0): rank one, r(g) = 0, and r_B <= 2.
 Clean reformulation of the r = 8 problem (exact, from the split agent's u-identities; u = t - (5/2)a):
   find linear a: V -> {col-centred}, b: V -> {row-centred}, a(al) has row means al, b(be) column means be, with
   (with E = average over the 25 cells, kappa = 25/9)
     E[a a'] = kappa E[al al'],  E[b b'] = kappa E[be be'],  E[a b] = 0,
     E[a a' a''] = kappa E[al al' al''],  E[b b' b''] = kappa E[be be' be''],
     E[a a' b] = 0,  E[a b b'] = 0.
   (Proof of equivalence: P_2, P_3 in u-coordinates; a = u_x, b = u_y up to the scale u = t - (5/2)a.)

STATUS 13:05: exact lemmas.
 (FK) If t in L (level) had column c equal to m*1 with m != 0, then perm(J + s t) = (1 + s m) Q(s), Q a
   polynomial (perm is linear in column c), = 120 for all s; s = -1/m gives 0 = 120. So psi_c(L) (column-c
   projection) meets C*1 only in 0; hence a functional n_c with n_c . 1 = 1 kills psi_c(L). Same for rows, and
   for any p x q block with p + q = 6 (Frobenius-Koenig: zero block => perm 0). [= 217's no_one_column, general n]
   Consequences: (a) L contains {y e_c^T : sum y = 0} => psi_c(L) contains V and avoids 1 => psi_c(L) = V =>
   every column-c sum is 0 on L => beta_c == 0 on L, r_B <= 3. (b) dim L = 9: ker of row-r projection >= 9-4 = 5;
   2x4 block: image avoids J_K so dim <= 7, kernel >= 2; 3x3 block: kernel >= 1.
   (c) In the r = 8 case write n_c = 1/5 + nt_c, m_r = 1/5 + mt_r (nt, mt in V), eps_c = e_c - 1/5,
   Q_c = nt_c (x) eps_c, Q'_r = eps_r (x) mt_r (DC). FK on x_B(be), x_A(al) gives
     Gamma_B^T Q_c = -eps_c, Gamma_A^T Q_c = -nt_c, Gamma_A^T Q'_r = -eps_r, Gamma_B^T Q'_r = -mt_r,
   so nt_c != 0, mt_r != 0 for all c, r, and with P_2 (Gamma^T Gamma = 20, Gamma_A^T Gamma_B = 0) the residues
   R = projection to (W_A + W_B)^perp in DC (8-dim) have Gram
     <R_c,R_c'> = (nt_c.nt_c')(eps_c.eps_c') - (nt_c.nt_c' + eps_c.eps_c')/20,
     <R_c,R'_r> = nt_c[r] mt_r[c] - (nt_c[r] + mt_r[c])/20,  (rows symmetric),
   10 vectors in an 8-dim space => this 10x10 Gram has rank <= 8. No contradiction extracted yet (needs P_3).
 (CC) Column-centred t (all column sums 0), rows t_i, G = t^T t, T_abc = sum_i t_ia t_ib t_ic:
     P_2 = -sum_i e_2(t_i),  P_3 = 2 sum_i e_3(t_i),
     P_4 = -6 sum_i e_4(t_i) + sum_{|C|=4} (G_ab G_cd + G_ac G_bd + G_ad G_bc),
     P_5 = 24 sum_i e_5(t_i) - 2 sum_{a<b} G_ab T_{complement of a,b}.
   Proof: P_k = sum_{|C|=k} sum_{pi partition of C} mu(pi) prod_blocks (sum_i prod_{j in block} t_ij); singleton
   blocks are column sums = 0. (lowd/ccform.py, error 1e-13.) For general t (entry sum 0, col sums 5 be_j, row
   sums s_i) the same expansion gives P_2 = 25 e_2(be) - sum_i e_2(t_i).
 (AB) Exact reformulation of "r = 8 with P_2 = P_3 = 0" (u = t - (5/2)(al (x) 1 + 1 (x) be), E = mean over cells,
   kappa = 25/9): linear a: V -> col-centred, b: V -> row-centred, row means of a(al) = al, column means of
   b(be) = be, with E[aa'] = k E[al al'], E[bb'] = k E[be be'], E[ab] = 0, E[aa'a''] = k E[al al' al''],
   E[bb'b''] = k E[be be' be''], E[aa'b] = 0 = E[abb'].  Equivalently Pi_B(aa') = 0, Pi_A(bb') = 0 where
   Pi_B = orthogonal projection on U_B; Pi_B(f(j)) = b(f)/kappa for column functions f.
 Numerics (all in lowd/): d1lm.py, d1lm2.py (d=1 graph spaces by (k,j) components), r8lm.py / r8lm2.py (r=8,
   bidegree components), aonto.py (alpha-onto + DC), ccg.py + chkC.py (column-centred + DC), rdlm.py
   (d=2, r=7: LM calibration on the known ex.1 configuration FAILED, so its negatives mean nothing).
 NEXT STEP suggestions: (1) r != 8: use FK (c) + P_3 cross identities E[aa'b] = 0 traced against the FK
   vectors (the Q_c, Q'_r are explicit DC test matrices tied to Gamma_A, Gamma_B), or find a computer-checkable
   certificate on the 128-variable system restricted by FK (40 more linear equations). (2) d=2 needs r <= 6:
   a calibrated search (seed with ex.1 / rc45) before believing any negative.
 (FK)(d) [exact] In the r = 8 case (any d): nt_c != 0 for every c (else beta_c == 0 on X_B), so psi_c(X_A) lies in
   the 3-dim space V cap nt_c^perp; hence for every column c there is a nonzero z_c in X_A (beta = 0) whose
   column c is identically 0 (the 4x4 map I + pi_c Gamma_A is singular).  Rows: w_r in X_B with row r = 0.
   [No contradiction derived from this yet.]
 Generalised no_glue (n = 5, via FK(a)): a level space cannot contain both a full one-column space {y e_c^T}
   and a full one-row space {e_r w^T} (FK(a) forces column-c sums 0, but e_r w^T has column-c sum w_c).
STATUS 13:12: more numerics. (i) FK + P_2 (rows/cols + all 2x4, 4x2 blocks, 916 eqs / 868 unknowns,
 lowd/fklm.py) is FEASIBLE for r = 8 (2/2 starts, 1e-14): FK does not replace P_3.  (ii) Calibration for the r=8
 negative: r = 7 (V + {be_4=0}, L080 type) with P2,P3 found 3/3, V + generic hyperplane 1/3 (lowd/r7cal.py);
 r = 8 found 0/7.  (iii) R7 above (P2,P3 alone, dim 8 not found anywhere).
STATUS 13:13: final. Extra: two rank-one root-of-unity families {x v^T : x.v'=0} + {v' z^T : z.v=0} (v, v' 5th-root
 vectors) give only dim 7 (overlap v' v^T) and violate P_3 cross terms (lowd/rk1fam.py) -- not a P2/P3 8-space.
 A Fermat rescaling (al, be -> (3i/4)(a, b)) makes P_2 = E[w^2] exactly but P_3 is then NOT E[w^3]
 (coefficients 9i/4, -27/8, 3i/4 vs 3, 6, 1), so no direct Kneser/L061 argument.
 Best next step: prove "no 9-dim subspace of the 24-dim sum-zero space is totally isotropic for P_2 and P_3"
 (or the narrower r != 8 statement in the (a,b) form), e.g. via an exact certificate on a normalised chart;
 for d >= 2 run a CALIBRATED search (the ex.1 calibration failed here).
