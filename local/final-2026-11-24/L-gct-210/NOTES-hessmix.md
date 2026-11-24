# NOTES-hessmix (role hessmix: Hessian-image orthogonality for FULL level spaces, aim (S))
## NEW RIGOROUS LEMMA (13:16) "rank-one column block caps r at 7" (uses only P_2 = P_3 = 0; hand proof below)
 Let L be level (P_2 = P_3 = 0 suffice) and suppose L contains B_v := {x v^T : sum x = 0} for some v with sum v != 0
 (L080 contains it with v = e_0). Then r <= 7 (so dim L <= 7 + d).
 Proof. u-image of x v^T is x w^T, w := c(v - (sum v/2) 1), normalised sum w = 1; so Y_A := Phi(B_v) = C^5_0 (x) w has R = x, C = 0.
 Let Y_B := {y in Y = Phi(L): R_y = 0}; (R,C)(Y) = C^5_0 x C(Y_B), so r = 4 + dim C(Y_B); suppose dim C(Y_B) = 4.
 Polarised u-identities (item 1): <y,y'> = (5/9)(R.R'+C.C'),  sum y y' y'' = (1/9)(sum RR'R'' + sum CC'C'').
 (i) (y,y' in Y_A, X in Y_B): sum_i (x*x')_i (X w^2)_i = 0 for all sum-zero x,x'; products x*x' span C^5, so X w^2 = 0;
     also X 1 = 0. If w^2 is not in C1, every row of X and hence C(X) lies in the 3-dim {1,w^2}^perp: contradiction.
 (ii) If w^2 = s^2 1: w_j = +-s, sum w = 1 and (Q on Y_A) 5 s^2 = 5/9 force w = (1/3)(1 - 2 e_{j0}); WLOG j0 = 0.
     (Q, Y_A vs Y_B): x^T X w = 0 for all sum-zero x => X w in C1 => column 0 of X is constant, = kappa_X.
     (T, Y_A Y_B Y_B): sum_j w_j X_ij X'_ij independent of i => x_i.x'_i =: m(X,X') independent of i (x_i = row i, cols 1..4).
     (Q, Y_B): 5 kappa kappa' + 5 m = (5/9)(25 kappa kappa' + c.c'), c := (C_1..C_4); and kappa = -(c.1)/5 (C_0 = 5 kappa, sum C = 0).
     Choose a 4-dim Y_B' in Y_B with X -> c an isomorphism onto C^4 and write x_i = M_i c. Then for each i:
        M_i^T M_i = K := (1/9) I + (16/225) 1 1^T   and   M_i^T 1 = (1/5) 1   (row sums zero: x_i.1 = -kappa = (c.1)/5).
     K is invertible so M := M_i is invertible and M^{-T} = M K^{-1}; K 1 = (89/225) 1. Hence 1 = (1/5) M^{-T} 1 = (45/89) M 1,
     so 1^T M 1 = (89/45)*4 = 356/45, while 1^T M 1 = (M^T 1).1 = 4/5 = 36/45. Contradiction. QED.
 Sanity: L080 (r = 7) realises the boundary: Y_B 3-dim, kappa = 0, M_0 = -(1/3)I, M_i = (1/3)I on 1^perp. LM (hessmix/rk1.py):
 with Y_A fixed, 3-dim Y_B found (4/4 starts, 1e-15); 4-dim: 4/4 starts stall at 7.8e-2.
 Scope: only spaces containing a full rank-one column block; general Y_A = {rho/5 (x) 1 + Gamma rho} is open (r = 8 from P2,P3
 is numerically infeasible; minimal infeasible block set = {Q-AA, Q-AB, Q-BB, T-AAA, T-AAB, T-ABB}: dropping ANY one of them
 makes r = 8 feasible to 1e-15 (2 starts each, hessmix/r8sub.py); with all six: 4 starts stall at 4e-3..1.2e-2).

 EXTENSION (rigorous, same notation; checked numerically on ex1/ex2/rc45 transposed, hessmix/blk.py): for L level containing a
 full column block (so w = (1/3)(1-2e_{j0})), put q := dim C(Y_B) = r - 4 and phi_i : Y_B -> C^4, X -> row i of X off column j0.
 Then phi_i^T phi_i = Ktilde := (c -> c^T K c') pulled back, of rank q with radical exactly D (= Y_B cap DC). Hence for every i:
 dim phi_i(Y_B) <= (4+q)/2 and phi_i(D) lies in the radical of phi_i(Y_B), so rank(phi_i|_D) <= floor((4-q)/2).
   q = 4 impossible (lemma);  q = 3 (r = 7) => phi_i(D) = 0 for all i => D = 0, i.e. (r,d) = (7,0) only.
 So a level space with a full row/column block has dim <= 8 unless (r,d) in {(6,>=3),(5,>=4),(4,>=5)}; those cases still need
 the DC conditions (P_4, P_5 on D: e.g. q = 2 gives D inside {sum_i e_i (x) lambda_i nu_i}, nu_i isotropic, nu_i perp 1).
 (Examples: ex2 = (q=2,d=1), ex1 = (1,2), rc45 = (0,2) after transposing; per-row ranks of phi_i|_D are [1,1,0,0,0], [1,1,1,1,0],
 [1,1,1,1,0] -- within the bounds 1, 1, 2.)

## RESULT (12:58) -- (S) NOT proved in any new case. Exact tools, one reformulation, several rigorous lemmas, negatives.
 1. EXACT u-COORDINATES (u = Phi(t) := g - (3/2)(alpha_i+beta_j); R, C = row/col sums of u; r_i, c_j = row/col sums of u*u).
    EXACT over Q (Fraction check at 12 random integer sum-zero points, hessmix/exactchk.py; deg <= 4 => Schwartz-Zippel):
      2P_2 = sum u^2 - (5/9)(sum R^2 + sum C^2)
       P_3 = (2/3)[ sum u^3 - (1/9)(sum R^3 + sum C^3) ]
       P_4 = (3/2)sum u^4 - (3/4)(sum r^2 + sum c^2) + p2(u)^2/8 + (1/4)tr((uu^T)^2)            [= DC formula]
             - (7/108)(sum R^4+sum C^4) + (7/216)((sum R^2)^2+(sum C^2)^2) + (1/36)sum R^2 sum C^2 - (1/12)p2(u)(sum R^2+sum C^2)
             + (1/2)(sum R_i^2 r_i + sum C_j^2 c_j) - (2/3)sum_ij (R_i+C_j)u_ij^3 + (2/9)sum_ij R_i u_ij^2 C_j
             - (1/9)(sum_i R_i^2 (uC)_i + sum_j C_j^2 (u^T R)_j) - (1/6)(|u^T R|^2 + |uC|^2) + (1/3)(sum_i (uC)_i r_i + sum_j (u^T R)_j c_j).
    Polarised P_2/P_3 on Y = Phi(L):  <y,y'> = (5/9)(R.R' + C.C'),  sum y y' y'' = (1/9)(sum RR'R'' + sum CC'C'').
    Hessians: H^3_t(s,s') = 4 sum Phi(t)Phi(s)Phi(s') + (375/2)(sum al_t al_s al_s' + sum be_t be_s be_s'); at DC delta:
      H^3_delta(s,s') = 4 sum delta u u' = 4<pi(delta*g),g'> - 6[al.rows(delta*g') + be.cols(delta*g') + (s<->s')] + 9(al^T delta be' + al'^T delta be).
      H^4_delta(s,s'): explicit formula in STATUS 12:45 below (checked 4e-15 at random DC delta).
 2. REFORMULATION (rigorous): for S inside L, W(S) := S + span{Q^{-1}Hess P_k(t)s : t,s in S, k=3..5} has W(S)^perp(Q) = E(S)
    := {y in V: grad P_k(t).y = 0 for t in S, k=2..5} (Euler: H^k_t(t,y) = (k-1)grad P_k(t).y; conversely differentiate).
    L is inside E(S). So every Hessian-image inequality = "dim E(S) >= l"; to kill l = 9 one must exhibit S inside L with dim E(S) <= 8.
    LEMMA G: any X inside L^perp(Q) has rank(Q|_X) <= 24 - 2l.  (dc5's Gram trick = X = M3_t L.)
 3. LEMMA (support, rigorous, TIGHT on every example): for delta in D with support S, Phi(L)|_S is totally isotropic for the
    nondegenerate form diag(delta|_S) (H^3_delta = 0 on L), so dim Phi(L)|_S <= |S|/2 and K_S := {s in L: Phi(s)|_S = 0} has
    dim >= l - |S|/2.  Equality dim Phi(L)|_S = |S|/2 holds in ex1, ex2, rc45 (|S| = 12, 6, 12): the extremal examples are
    LAGRANGIAN on supp(delta).
 4. LEMMA (cross product, rigorous): Y_A := {y in Y: C_y = 0}, Y_B := {y: R_y = 0} (dims l-r_B, l-r_A, Y_A cap Y_B = D).
    Then Y_A perp Y_B and the HONEST Hadamard product Y_A*Y_B is dot-orthogonal to Y; also GY perp Y (Gy = y-(5/9)(R_i+C_j)).
    Hence dim(C1 + GY + Y_A*Y_B) <= 25 - l, and with Kneser (dim XY >= dim X + dim Y - h, h = dim Stab):
        4l <= 24 + r_A + r_B + h + j,   j = dim((C1+GY) cap Y_A*Y_B).
    For l = 9 this needs h + j >= 4. USELESS IN PRACTICE: the 7-dim examples have h = 6 (block stabilisers), j = 3
    (L080: dim Y_A*Y_B = 12, ex1/ex2: 10). Any Kneser/product-dimension argument must first handle block-supported spaces.
 5. NEGATIVES: (a) full-L Lemma A fails (L + M3_t L not direct at generic t: L080, rc45, ex1). (b) dim W(S) >= 2 dim S + 2
    fails for small S (L080 line: 2, plane: 5) though it holds with equality (16) at all three 7-dim examples.
    (c) Local data at D is too weak for d = 1: ex2's delta (rank one, 3x2 support) has grad P4 = grad P5 = 0, Hess P5 = 0,
    rank Hess P3 = rank Hess P4 = 6; a 9-dim space through it isotropic for Q and all Hessians at delta appears to exist (LM res
    2e-6, weak). (d) The linear route "Y_B inside N(Y_A) = RC' cap (Y_A+Y_A*Y_A)^perp, isotropic for q_B" (for r = 8) fails:
    for L080's Y_A, dim(Rows+Y_A+Y_A*Y_A) = 9 only, N(Y_A) is 16-dim.  (e) ex1 is P2P3-maximal at first order+LM:
    E_{P2,P3}(ex1) has dim 10 but no P2P3 extension by 1 inside it (4 LM starts, res 0.53).
 NEXT STEP: the obstruction lives in block/support structure. Most promising: combine Lemma 3 (Lagrangian on supp delta) with
    H^4_delta on K_S, and Kneser's STRUCTURE theorem (block stabiliser) for Y_A*Y_B, as a case analysis on supports; or prove
    lowd's numerical claim "no 8-dim P2,P3-isotropic Y with r = 8" (which kills all (8,d)) in the u-coordinates of item 1.
STATUS 12:35: H3 at DC point verified: H^3_delta(s,s') = 4 sum delta*Phi(s)*Phi(s'), Phi(s)=g-(3/2)a (1e-14 on all examples). Generic-t Hessian images computed on L080/ex1/ex2/rc45/W5/S4. Testing conjecture dim(L+M3_t L) >= 2l-2 (would give l<=8).
STATUS 12:40: findings so far (all numerically verified, hessmix/t*.py):
 (H1) EXACT u-coordinate form of P2,P3 for FULL sum-zero t. u = Phi(t) := g - (3/2)(alpha_i+beta_j), R,C = row/col
      sums of u (R = -(15/2)alpha, C = -(15/2)beta):
        2 P_2(t) = sum u^2 - (5/9)(sum R_i^2 + sum C_j^2),     P_3(t) = (2/3)[ sum u^3 - (1/9)(sum R_i^3 + sum C_j^3) ].
      (err 1e-13). Equivalently, with iota(u) = (u, alpha_u, beta_u) in C^35 and weight -125/9 on the 10 mean
      coordinates, P_1,P_2,P_3 are the weighted power sums tr_w(iota(u)^k): level up to P_3 <=> iota(Phi L) is
      power-sum isotropic (k<=3) in the ASSOCIATIVE algebra (C^35, coordinatewise, tr_w). (Breaks at P_4.)
 (H2) Hessians: H^3_t(s,s') = 4 sum Phi(t)Phi(s)Phi(s') + (375/2)(sum al_t al_s al_s' + sum be_t be_s be_s').
      At delta in D: H^3_delta(s,s') = 4 sum delta*Phi(s)*Phi(s') (checked 1e-14).
 (H3) THE HESSIAN-IMAGE METHOD FOR FULL L IS EXACTLY THE FIRST-ORDER EXTENSION SPACE: with
      W := L + span{M^k_t s : t,s in L, k=3,4,5} (M^k_t = Q^{-1} Hess P_k(t)), W^perp(Q) = E(L) := {y : grad P_k(t).y = 0
      for all t in L} (H^k_t(t,y) = (k-1) grad P_k(t).y, and H^k_t(s,y) = D_s of it). So the method can only prove
      "dim E(L) small"; for l = 9 one needs dim W >= 16. Numerically dim W = 16 (dim E = 8) for ALL THREE 7-dim
      examples (L080, ex1, ex2); rc45: W 14 (E 10); W5: W 12.
 (H4) LEMMA G (rigorous, trivial): for ANY subspace X of L^perp, rank(Q|_X) <= 24 - 2l (image of X in the nondegenerate
      (24-2l)-dim space L^perp/L has dim >= rank Q|_X). With X = all Hessian images: rank Q|_X = 9 = (24-2l) - 1 for
      all three 7-dim examples. For l = 9 it would need rank <= 6.
 (H5) "Excess" e_t := dim(L + M3_t L) - l at generic t: for generic m-dim SUBSPACES of every example e_t = m (direct sum),
      but at the full space it drops: L080 7->5, rc45 6->4, ex1 7->6, ex2 7->7. So no "Lemma A" (L (+) M3_t L direct)
      for full L; L080 has ker M3_t|_L != 0 at generic t (rank M3_t L = 6). Conjecture "e_t >= l-2" (would give l<=8)
      has no structural support.
 (H6) Hessian forms at sparse delta are weak: ex2's delta (rank one, support 3x2) has rank H3 = rank H4 = 6, H5 = 0
      (rank of stacked [H3;H4;H5] = 11 on V). LM: a 9-dim subspace containing delta, isotropic for Q,H3_d,H4_d,H5_d,
      seems to EXIST (res 2e-6 decreasing, basis well-conditioned, trf not fully converged): the at-delta quadratic
      conditions alone cannot exclude (r,d) = (8,1). For ex1's delta (support 12) stalls at 8e-3 (2 starts, weak).
STATUS 12:45: EXACT P_4 FORMULA FOR FULL (sum-zero) t in u = Phi(t) coordinates (rel err 3e-14, hessmix/h4.py):
  P_4 = (3/2)sum u^4 - (3/4)(sum r_i^2 + sum c_j^2) + p2(u)^2/8 + (1/4)tr((u u^T)^2)          [= the DC formula]
      - (7/108)(sum R^4 + sum C^4) + (7/216)((sum R^2)^2 + (sum C^2)^2) + (1/36) sum R^2 sum C^2 - (1/12) p2(u)(sum R^2 + sum C^2)
      + (1/2)(sum_i R_i^2 r_i + sum_j C_j^2 c_j) - (2/3)(sum_ij R_i u_ij^3 + sum_ij C_j u_ij^3) + (2/9) sum_ij R_i u_ij^2 C_j
      - (1/9)(sum_i R_i^2 (uC)_i + sum_j C_j^2 (u^T R)_j) - (1/6)(|u^T R|^2 + |u C|^2) + (1/3)(sum_i (uC)_i r_i + sum_j (u^T R)_j c_j)
  (R, C = row/col sums of u; r_i, c_j = row/col sums of u*u; uC = u times C.)
  HESSIAN OF P_4 AT A DC POINT delta (u = Phi s, v = Phi s', R,C / R',C' their row/col sums, rho = rows(delta*u),
  kappa = cols(delta*u), rd = rows(delta^2), cd = cols(delta^2)); rel err 4e-15 at random DC delta:
  H^4_delta(s,s') = 18 sum delta^2 u v - 6 rho.rho' - 6 kappa.kappa' - 3 sum_i rd_i rows(u v)_i - 3 sum_j cd_j cols(u v)_j
      + <delta,u><delta,v> + (1/2)p2(delta)<u,v> + tr(delta^T delta u^T v) + tr(delta u^T delta v^T) + tr(v^T delta delta^T u)
      - (1/6)p2(delta)(R.R' + C.C') + sum_i rd_i R_i R'_i + sum_j cd_j C_j C'_j - 2 sum delta^2 (R_i v_ij + R'_i u_ij + C_j v_ij + C'_j u_ij)
      + (2/9) sum delta^2 (R_i C'_j + R'_i C_j) - (1/3)[(delta^T R).(delta^T R') + (delta C).(delta C')]
      + (2/3)[(delta C).rho' + (delta C').rho + (delta^T R).kappa' + (delta^T R').kappa]
      + (1/3)[sum_i rd_i ((vC)_i + (uC')_i) + sum_j cd_j ((v^T R)_j + (u^T R')_j)].
  On a level space with delta in D the 2nd-line terms with <delta,u> and p2(delta) vanish.
STATUS 12:56: (times above corrected). Read lowd: r=8 numerically infeasible from P2,P3 alone. Testing a linear-algebra route for r=8: Y_B lies in N(Y_A) = RC' cap (Y_A + Y_A*Y_A)^perp and is isotropic there for q_B = <y,y> - (5/9)|C|^2; if dim N(Y_A) <= 7 with q_B nondegenerate => dim Y_B <= 3 => r <= 7.
STATUS 12:58: wrote final RESULT (items 3,4 new: support Lemma, cross-product Lemma + Kneser numbers). hessmix/kn.py, nya.py, exactchk.py.
STATUS 13:05: (a) INDEPENDENT CONFIRMATION of lowd's "r = 8 impossible from P2,P3 alone", in the canonical u-parametrisation
 (hessmix/r8u.py: Y_A = {rho/5 (x) 1 + Gamma rho}, Y_B = {1 (x) sigma/5 + Delta sigma}, Gamma, Delta : C^5_0 -> DC, no gauge,
 equations = polarised (Q),(T) of item 1): calibration r = 7 (4+3, C-image a free 3-plane): 3/3 starts converge to 1e-15
 (well-conditioned); r = 8 (4+4): 5/5 starts stall at residual 1.7e-2 .. 3.8e-2 (min sv of basis ~0.6). In these coordinates
 (Q) reads: Gamma^T Gamma = Delta^T Delta = (16/45) Id, Gamma^T Delta = 0 (similitudes onto orthogonal 4-planes of DC);
 (T-AAB) reads: Delta^T pi(A rho * A rho') = -(1/5) colsums_0(A rho * A rho').
 (b) CASIMIR IDENTITY (rigorous, checked on L080 to 1e-16): if R maps Y_A onto C^5_0, c_A := sum_k A(rho_k)*A(rho_k^*) (dual bases)
 is dot-orthogonal to ALL of Y and has <c_A, 1> = 20/9 (from (T-AAA) contracted: (1/9)(4/5) sum R'' = 0, and (T-AAB)).
 Possible seed for a trace-identity proof of r <= 7.
 (c) MINI-LEMMA (rigorous, uses only (Q-AA),(T-AAA),(T-AAB)): if Y_A = C^5_0 (x) w (rank-one row block, as in L080) then
 sum w = 1, p2(w) = 5/9, p3(w) = 1/9, and every y in Y with R_y = 0 satisfies y w^2 = 0 (products rho*rho' span C^5), so its
 rows lie in {1, w^2}^perp and C(Y_B) has dim <= 3 unless w^2 in C1, i.e. w = (1/3)(1,1,1,1,-1) up to a column permutation
 (exactly L080's row block). In that case Y_A perp Y_B forces column 0 (the -1 column) of every X in Y_B to be constant, and
 (T-ABB) forces sum_{j>=1} X_ij X'_ij to be independent of i. (Not finished: expected dim count -2 for a 4-dim Y_B.)
STATUS 13:16: rank-one column block lemma proved (top). r=8 minimal infeasible block set identified (all six blocks needed).
STATUS 13:15: block extension (r=7 => d=0 when a full row/column block is present) proved + checked. Writing final report.
STATUS 13:17: partial analysis of the remaining block case q = 2 (r = 6, need d <= 2): phi_i(D) inside C nu_i, nu_i isotropic, nu_i perp 1;
 d <= |I| - rank{nu_i}. rank 3 => d <= 2 OK. rank 1 => D = {lambda (x) nu~ : lambda in Lambda}, rank-one DC, e1(nu~) = e2(nu~) = 0;
 if e3(nu~) != 0 then p3 == 0 on Lambda inside C^5_0 (Clebsch diagonal cubic surface, smooth => no planes) => d <= 2 OK;
 if e3(nu~) = 0, e4(nu~) != 0 (nu ~ 4th roots of unity) need: no 3-dim Lambda in C^5_0 with e4 == 0 (OPEN, plus unused constraints);
 rank 2 (two isotropic directions, rows split) d <= 3: OPEN. LM check of the lemma (Y_A fixed): 3-dim Y_B 4/4 starts 1e-15; 4-dim Y_B 4/4 starts stall at the SAME value 7.8e-2 (consistent with the proof).
