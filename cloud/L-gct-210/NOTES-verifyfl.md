# NOTES-verifyfl (role: verifyfl; start 14:17, budget 80 min)

## RESULT ROUND 5 (verifyfl, 19:14-20:54; details in section DI5-R5; compute requests in COMPUTE-verifyfl.md)

 (SL_m) IS NOT PROVED IN ANY FULL STRATUM.  It is reduced, for |supp m| = 3 and m non-isotropic, to four explicit residual kinds.
 All items G1-G6 are rigorous hand proofs (R = rigorous); numerics are flagged (N).
 G1 (R) Lemma C' (R5.1): column form with defect; which blueprint lemmas survive: for a NEUTRAL column n (m_n = 0) Lemma N, (B1), (B3),
        (B-i), (B-ii) hold verbatim for that column; for columns of P one has the pencil <z_j,z_j> = vartheta m_j on the doubly centred
        part N and b_j^*g = s^*g + 4 m_j vartheta; (B-i) fails (q = 3 does not force N = 0); Lemma A and S6-S8 must be redone.
 G2 (R) Lemma 3C (R5.2), ANY m with |supp m| = 3: a column-centred space with defect in C m all of whose matrices vanish on the two
        neutral columns has dim <= 3.  (Proof: a diagonalising change of columns turns the three quadratic conditions into
        <Y'_j,Y'_j> = vartheta'' m_j^2; rank analysis; the rank-1 case dies on the mu t^2 terms of tau(y_a y_b y_c).)
 G3 (R) Lemma NP (R5.3): N_P := doubly centred part supported on P.  m non-isotropic: dim N_P <= 2, and dim 2 only for TYPE I'
        chi_1 (x) W_P or the NEW TYPE V  chi_1 (x) c^+ (+) chi_3 (x) c^-  (c^+- the two roots of m_a l_b l_c + m_b l_a l_c + m_c l_a l_b on
        zero-sum l) - an exact family of doubly centred (2,1) spaces for EVERY non-isotropic 3-support m.  m isotropic: dim N_P <= 3;
        U_2 (x) (1/m), U_2 = {(x,y,-x,-y)}, is an exact doubly centred (2,1) space.
 G4 (R) Lemma T (R5.4): if chi_1 l^T is in K (l zero-sum on P, no zero entry, l not proportional to 1/m) then on ALL of K the neutral
        columns are y_n = k chi_2 + rho_n chi_3, y_n' = -k chi_2 + rho_n' chi_3 with rho_n rho_n' == 0.   (t-top-degree coefficients of
        the cubic and quartic conditions; four coefficient identities, checked numerically.)
 G5 (R) Prop I' (any m): K containing chi_1 (x) W_P has dim <= 3.   Prop V (m non-isotropic): if N_P is of type V then K is 3-column,
        dim <= 3.   (R5.5)
 G6 (R) THEOREM SL3-RED (R5.6): |supp m| = 3, m non-isotropic, dim K = 4  ==>  dim N_P <= 1 and K is of kind
          (R1) type (3,1), N = C Z_* supported on P with vartheta(Z_*) != 0;
          (R2) type (3,1), m proportional to (1,1,-2,0,0) and N = C v (e_a - e_b)^T on the two equal columns;
          (R3) type (2,2), S = u^perp (u isotropic), a neutral column active on N;
          (R4) type (1,3), both neutral columns active on N, dim N_P = 1.
        Excluded: type (0,4); every K with dim N_P = 2; type (3,1) with vartheta(Z_*) = 0 unless (R2).
        (R3) is the analogue of blueprint S7/S8 and is where the two-column counterexamples live ((N): a climb for m = (1,-1,0,0,0)
        reaches a column-centred (4,1) space of type (2,2)); so it is the place where "not two-column" must enter.
 G6' (R) Props I-ALL and II-ALL (R5.9): for |supp m| = 3 a K containing a blueprint type I plane chi_1 (x) Lam_M (ANY 3-set M of columns)
        or a type II plane mu v (e_i - e_j)^T + mu' v' (e_k - e_l)^T (any position; m non-isotropic) has dim <= 3.  So the two extremal
        configurations of blueprint S7/S8 are excluded; the proof shows exactly where two-column m escapes (theta_3 (m_i + m_j) = 0 does
        not force theta_3 = 0 when m = e_i - e_j).  (N) calibrated: climbs from the type II plane reach dim 4 for m = (1,-1,0,0,0) in 3/3
        runs and stop at dim 3 for (1,2,-3,0,0), (1,1,-2,0,0) in 6/6 runs.
 G7 (R) |supp m| >= 4 with four distinct nonzero entries, type (3,1): the pencil forces vartheta(Z_*) = 0, Theta(.,Z_*) = <phi,s(.)> with
        phi isotropic, phi != 0 (R5.7).  Nothing else proved for |supp m| = 4, 5 or for isotropic m (status list in R5.7).
 (N) Sanity/landscape: 3-column spaces of dim 3 abundant, dim 4 never (0/100); 3-dim column-centred spaces with defect are plentiful
     and of type (3,0) (R5.8); for m = (1,1,-2,0,0) climbs from v (e_a - e_b)^T stop at dim <= 3.
 COMPUTE-verifyfl.md (for the 24-core machine): A isotropic planes N maximal (exact, small, decides the principal isotropic (5,1));
     B the N-problem for |P| = 4, 5 (exact); C calibrated Gr(4,15); D direct (5,1); E extension varieties of explicit planes; F typed
     searches for (R1)-(R4).

## RESULT ROUND 4 (verifyfl, 18:20-19:50; details in section DI5-R4)

 (DI_5) AT e = 1 IS STILL NOT PROVED.  New this round (R = rigorous, N = numerical only):
 F1 (R) Lemma QB: the quadratic normal form with defect, on all of L' and for any m:
        <b_j,b_j> = <s,s> + 3 kappa^2 m_j^2 - 2 thetahat_2 m_j (j = 1..5), sum_a <y_a,y_a> = <s,s> + kappa^2 <m,m>.  [R4.1; general e stated]
 F2 (R) Theorem PS (principal stratum): if ker kappa contains a 3-dim strongly level H with s(H) = V (the only kind of ker kappa seen in the
        35 known (4,1) spaces with good = non-two-column, non-isotropic m), then L' = H (+) N, N = ker s, with z_j = m_j((kappa/4)1 - 2 B_j f_Z), f : N -> V injective,
        <f_Z,f_Z> = (3/16) kappa(Z)^2; hence dim N <= 2 and dim L' <= 5, and a (5,1) is H (+) C Z (+) C Z_* with f_* isotropic, <f,f_*> = 0. [R4.3]
 F3 (R) Lemma PR-RED: "every (4,1) with principal ker kappa is split" => no (5,1) with a principal H.  [R4.4]
 F4 (R) THEOREM PR3: for m NON-ISOTROPIC with |supp m| = 3 there is NO (5,1) space whose ker kappa contains a principal H.
        Proof by hand: Z_* = chi_1 l^T, Z = h_0 m^T + chi_1 alpha^T, h_0 = (1/4)1 +- (sqrt 3/4) chi_2, and the neutral deletion gives
        kappa (4 beta Q_m(lam) - (3/8) e_3(m) kappa^2) = 0 on a plane; the quadratic form has rank 3 unless <m,m> = 0.  [R4.5]
        For ISOTROPIC m = (1,w,w^2,0,0) the same computation produces four explicit non-split 2-dim level spaces N with defect line C m
        (Z_* = chi_1 (1/m)^T); (N) they have no extension at all (0/60 calibrated starts).
 F5 (R) Clean target (SL_m): "a column-centred 4 x 5 space with deletion vectors in 24*1 + C m has dim <= 3" for non-two-column m implies
        (DI_5) at e = 1 in ALL remaining cases (split, non-split, isotropic), because ker kappa of a (5,1) is such a space of dim 4.
        False for two-column m (numerical examples; all 42 stored (4,1) spaces with other m have kappa != 0).  [R4.2]   (N) Gr(4,15) searches: 0 hits for five m (isotropic with 3, 4, 5 support; (1,2,3,-1,-5);
        (1,2,-3,0,0)), but the positive control succeeds only at 3/82 starts - WEAK evidence, do not rely on it.  [R4.7]
 F6 (R) The suggested tricks give nothing new: m in two slots (isotropic split) reproduces only the linear conditions; Lemma EQ over all column
        pairs is equivalent to the definition of the defect line; rows' "dim Pi_0 <= 2" would settle the isotropic split case only for |supp m| >= 4.  [R4.6]
 F7 (N) The N-problem (R4.3) for |supp m| = 4, 5: no solution found for distinct entries (0 injective among 19, 20, 11, 15 hits); for
        (1,2,-4,1,0) (repeated entry) solutions exist but do not extend to dimension 3 (0/64).  Calibrated by |P| = 3 (PR3: 0/169 vs 50/243).
 OPEN: (o1) principal (5,1) for |supp m| >= 4 or isotropic m (reduced to the N-problem, a small exact computation, plus "N does not extend");
       (o2) non-principal (5,1) = (SL_m) outside the principal stratum (needs the cubic/quartic case analysis with the extra form; not done).
 e = 2, 3: only the normal form of PS generalises (R4.8); it gives no bound for (6,2), (7,3).  FS and TS remain the only rigorous results there.
 Round 3's hand-back was cut off; its results are RESULT ROUND 3 below (unchanged).

## RESULT ROUND 3 (verifyfl, task "split case of (5,1)"; final 18:10) -- split case SETTLED for non-isotropic m; (5,1) in general still open
 E1 [RIGOROUS, 3 lines] THEOREM SPLIT (R3.1): if a 4x5 space with defect line C m contains e_i m^T and <m,m> != 0, then
    thetahat = kappa * mu on L' (mu = eigenvalue of the symmetric cofactor matrix D_i(Y) on m), so ker kappa is strongly level and dim L' <= 4.
    Tool: <w,C(Y)> = Per(l_1,..,l_4,w) is a SYMMETRIC 5-linear form; move m from the test slot into row i.
 E2' [RIGOROUS] THEOREM TS (R3.2'), e = 2 split over two rows (C = Cu + Cu', e_i u^T, e_k u'^T in L', nondegenerate): on ker(column sums)
    c(Y) = <y^i,u'><y^k,u> D_ik(Y)(u,u')/(<u,u><u',u'>); so dim L' <= 6, and a (6,2) space of this kind has a very rigid shape (not excluded).
 E2 [RIGOROUS] THEOREM FS (R3.2), any e: if one row carries the whole defect space (e_i (x) C(L') in L') and <,> is nondegenerate on C(L'),
    then c(Y) = D_i(Y) gamma(Y), ker(column sums) is strongly level and dim L' <= e + 3: no (6,2), (7,3) of this kind.
 E3 [RIGOROUS] LEMMA HYP (R3.3): every hyperplane of a (5,1) space is a (4,1) space with the same m; so "every (4,1) space with defect
    line C m is split" would exclude (5,1) for that m.  With E1 + TC5, (DI_5) at e = 1 is reduced to (NS4')/(K4)/(K4')/(ISO) of R3.5.
 E4 [NUMERICAL] (a) all 35 known (4,1) spaces with non-two-column, non-isotropic m are split with ker kappa strongly level of type (3,0);
    non-split spaces are common in dimension 3. (b) For ISOTROPIC m, e.g. (1,w,w^2,0,0), the conclusion of E1 FAILS: there are split (4,1) spaces
    with ker kappa not strongly level (a new kind of 7-dim level space, level error 1.7e-13), so <m,m> != 0 is necessary; split (5,1) with
    isotropic m: not found (0 of about 460 extension starts over three isotropic m), not excluded.
 E5 stage3's N2 line eta: excluded by my tools only if eta is two-column, or if L^j is split along a non-isotropic eta (R3.6); otherwise N2
    needs the non-split case.
 E6 [NUMERICAL] column-centred (kappa == 0) spaces with a good defect line exist up to dimension 3 and then stop: the four 3-dim ones tested do
    not extend to dimension 4 (0/56, calibrated). Exact sufficient statements for the rest of (DI_5) at e = 1: (NS4'), (K4)+(K4'), (E3) in R3.5.
 NOT PROVED: (5,1) non-split with non-two-column m (the dichotomy), isotropic split case, split over several rows for e = 2, 3.

## RESULT ROUND 2 (verifyfl, task "(DI_5) at e = 1"; final 16:35) -- (DI_5) at e = 1 is NOT proved in general. Proved / found:
 D1 [RIGOROUS, any m] LEMMA EQ: in a 4x5 space with defect line C m, every subspace fixed by a column permutation that moves m is
    STRONGLY level; in particular {y_a = y_b} for m_a != m_b has dim <= 3 (Lemma SL).  (Section DI5.1; checked on 24 examples.)
 D2 [RIGOROUS] THEOREM TC5: no (5,1) space with a TWO-COLUMN defect line m = e_a - e_b;
    i.e. no 8-dim level space with a deletable row whose defect line is e_a - e_b.  Proof = symmetrised normal form (DI5.2: the defect
    conditions become "strongly level with corrections quadratic in d = (y_a - y_b)/2") + dim L' = q + dim Nbar + dim zeta + five lemmas
    (Lagrangian lemma, neutral isometries, dim Nbar <= 2, and the exclusion of (2,2,1)).  One step uses exact computer arithmetic: the
    resultant identity Res_u = -(3/256)(t^8 - 56t^4 + 16)^3 (verifyfl/di_res_exact.py); everything else is by hand.  The only (5,1) candidate type is (q, dim Nbar, dim zeta) = (2,2,1), and it is excluded; the 4-dim types
    (3,0,1), (2,1,1), (1,1,2), (1,2,1) all occur (examples), so the proof excludes nothing that exists.
 D3 [EXACT, new] two new (4,1) spaces (DI5.4): chi_1 (x) C^{345} (+) C e_i(e_1-e_2)^T (split, kernel of type (1,2)), and a third kind: span{uh(e_0-e_3)^T, z_1(e_0-e_3)^T, ub e_1^T, ub e_4^T}; contains rows' M_2; kappa != 0
    but ker kappa NOT strongly level; gives a 7-dim level space. So "kappa != 0 => ker kappa strongly level" is false (it holds in 22/24 examples).
 D4 [assessment] general m and e = 2, 3: DI5.6. The two-column case is special (theta drops out); the 22 general-m examples are all "split"
    (contain e_i m^T) and belong to rows' 3-row formulation. Induction on e via {y_a = y_b} needs the trade-off dim L'' + dim D <= e + 3, which is
    what TC5 proves for e = 1 two-column; no uniform argument found.
 NUMERICAL ONLY: Gr(5,17) search 0/84 (calibrated at 15%); the split/two-column dichotomy of the known (4,1) spaces; the census numbers.

## RESULT (verifyfl, round 1): THEOREM FL IS CORRECT -- every step re-derived independently; verdict VERIFIED on all steps
 Claim checked (NOTES-zeros, RESULT 1/2/4): a 5x5 level space containing a full free row F_r = {e_r w^T : sum w = 0}
 (or a full free column) has dim <= 7.  I re-derived the reduction and Lemma SL from scratch (own notation, own proofs),
 tested every identity at random complex points (<= 3e-14), and ran calibrated numerical tests of the exclusions.
 No hole found. Two imprecisions in the write-up, both harmless and repaired below:
   (a) TYPE III: "C3 on {a,b} gives tau(v v'^2) = 0" fails when e_2(n) = 0 (e.g. n = (1,w,w^2)); that equation is not
       needed (the write-up's own closing remark says so). My Lemma G23 below needs no sub-cases at all.
   (b) (not an error, a reader's trap) TYPE II "t mu'^2 coefficient of C3_a" and TYPE IV "mu^2 coefficient of C3_c" are
       stated for the NORMALISED equations (C3_m minus half the sum of all C3, the write-up's w-form); for the raw
       P_3(Y^(m)) the same coefficients carry an extra term (I fell into this in my first numerical test). The blueprint
       below uses the deletion of the INACTIVE column for type II (raw equation, no normalisation needed).
   Also "C3 on M2 forces tau(v'^3) = 0" in type III is right only in the normalised form; raw, it is T_a + T_b.
 Per-step verdicts:
   reduction L = F_r (+) L', L' strongly level, and converse ............ VERIFIED (S1; test1.py on 9 examples)
   column form C1-C4 of strong levelness ................................ VERIFIED (S2; test2.py)
   columns of N isotropic lines, N inside K ............................. VERIFIED (S3)
   dim N <= 2 ........................................................... VERIFIED (S4; simpler proof for g = 1)
   completeness of types I-IV for dim N = 2 ............................. VERIFIED (S4)
   q = 3 => N = 0; q = 2, N != 0 => S = u^perp; b_m in C v_m ............ VERIFIED (S5; test4.py on examples)
   types III, IV do not exist ........................................... VERIFIED (S6; III after repair (a))
   type II = ex1 plane, excluded ........................................ VERIFIED (S7; after rewording (b))
   type I excluded ...................................................... VERIFIED (S8; shorter final step)
 Numerical evidence (verifyfl/*.py, each run <= 125 s CPU, most < 30 s): 33 identities to 3e-14; all closed forms of the exclusions to 1e-12;
   Newton finds all 17 affine solutions of tau(v v'^2) = tau(v^2 v') = 0, exactly the 8 common-zero-row ones have perm = 0;
   CALIBRATED extension searches: type II plane -> only N + C(1,1,1,-3)^T e_4^T (7/16 starts, all there);
   type I plane -> only chi_1 (x) C^M (7/16, all there); chi_1 (x) C^M -> no extension with P_4 (0/12) but 6/6 without P_4;
   all 10 known 3-dim strongly level spaces: random plane re-extends (5-6/6), the space itself never (0/10).
   Classification-free structured search (flag.py; N in a DC chart, row sums of the other vectors dual-normalised):
   (q,d) = (2,1): 10/12 starts converge, (1,2): 1/10, (2,2): 0/40  -- a calibrated negative for the excluded case.
   DC planes from random starts (35 hits): 34 x type II, 1 x type I, nothing else (no type III/IV).
   Identities also verified EXACTLY (Gaussian-rational arithmetic) at random points (test5_exact.py, test6_exact.py).
   Unstructured random-start LM negatives at dim 4 are uncalibrated and NOT used.
   Status of the proof: hand proof, re-derived and machine-tested, NOT Lean-checked.
 Deliverable: complete self-contained proof = sections S0-S9 below (blueprint for Lean), identity list in S10.

## BLUEPRINT: complete proof of Theorem FL

### S0 Conventions
 C^4 with coordinatewise (Hadamard) product; tau(x) = x_0+x_1+x_2+x_3; <a,b> = tau(ab); V = {x in C^4 : tau(x) = 0}
 (dim 3; <,> is nondegenerate on V since C^4 = V (+) C(1,1,1,1) orthogonally).  "isotropic" = <x,x> = 0.
 Bracket of four vectors of V:  [y1,y2,y3,y4] := -6 tau(y1y2y3y4) + <y1,y2><y3,y4> + <y1,y3><y2,y4> + <y1,y4><y2,y3>.
 A 4x5 matrix Y has columns y_1..y_5 in C^4, row-sum vector s(Y) = sum_m y_m, deletions Y^(m) (4x4, column m removed).
 A 4x4 matrix Z is level if perm(J_4 + cZ) = 24 for all c in C. A LINEAR space L' of 4x5 matrices is STRONGLY LEVEL
 if every Y^(m), Y in L', is level (for a linear space: perm(J_4 + Y^(m)) = 24 for all Y, m suffices).
 Characters chi_a = (i^{ak})_{k=0..3}: chi_a chi_b = chi_{a+b}, chi_{a+4} = chi_a, tau(chi_a) = 4 if 4 | a, else 0.
 V = span(chi_1, chi_2, chi_3); for v = p chi_1 + q chi_2 + r chi_3:  <v,chi_1> = 4r, <v,chi_2> = 4q, <v,chi_3> = 4p,
 <v,v> = 8pr + 4q^2.  So chi_1, chi_3 are isotropic, and v isotropic with p = 0 (or with q = 0 = <v,chi_2>) is in
 C chi_3 (resp. in C chi_1 u C chi_3).  zeta := (1, w, w^2, 0), w = exp(2 pi i/3): zeta, conj(zeta) isotropic in V,
 zeta^2 = conj(zeta), conj(zeta)^2 = zeta.
 Row permutations (S_4 acting on C^4) and rescaling preserve everything above and strong levelness.
 "f == 0 on a linear space W" for a polynomial f means identically; products of nonzero polynomials on W are nonzero.

### S1 Reduction (uses only multilinearity of perm in a row)
 PROP R. Let L be a level space of 5x5 matrices with F_5 = {e_5 w^T : sum w = 0} inside L. Then every y in L has
 row-5 sum 0, L = F_5 (+) L' with L' = {y in L : row 5 of y = 0} (viewed as 4x5 matrices), and L' is strongly level;
 dim L = 4 + dim L'. Conversely F_5 (+) L' is level for every strongly level L'. (Other rows: permute; columns: transpose.)
 Proof. For y in L, c in C, w with sum w = 0: cy + e_5 w^T in L. Expanding along row 5 (ID1):
   perm(J + cy + e_5 w^T) = sum_j (1 + c y_5j + w_j) C_j(c),   C_j(c) := perm(J_4 + c Y^(j)),  Y = rows 1..4 of y.
 The value is 120 for all sum-zero w, so sum_j w_j C_j(c) = 0, i.e. C_j(c) = C(c) for all j; then
 120 = (5 + c rho) C(c) with rho = sum_j y_5j, a polynomial identity in c; so 5 + c rho has no root, rho = 0, C == 24.
 Hence y - e_5 (row 5 of y)^T is in L with zero row 5: L = F_5 (+) L'; and for Y in L' all C_j == 24: strongly level.
 Converse: perm(J + Y + e_5 w^T) = sum_j (1 + w_j) 24 = 120.  QED

### S2 Column form of strong levelness
 LEMMA C. Let L' be a linear space of 4x5 matrices. L' is strongly level iff for all Y in L' and all m in [5]:
   (C1) tau(y_m) = 0 (all columns in V);
   (C2_m) q_m(Y) := <y_m,y_m> - <s(Y),y_m> = 0;
   (C3_m) T_m(Y) := sum over triples {a<b<c} not containing m of tau(y_a y_b y_c) = 0;
   (C4_m) [y_a,y_b,y_c,y_d] = 0 where {a,b,c,d} = [5] \ {m}.
 Proof. (ID2) for a 4x4 matrix Z with columns z_a: perm(J_4 + cZ) = 24 + 6c (sum of entries) + O(c^2), and if all
 tau(z_a) = 0:  perm(J_4 + cZ) = 24 - 2c^2 sum_{a<b} <z_a,z_b> + 2c^3 sum_{a<b<c} tau(z_a z_b z_c) + c^4 [z_1,z_2,z_3,z_4].
 (Sum over injective row choices = sum over set partitions with Moebius weights (-1)^{|B|-1}(|B|-1)!; singleton blocks
 vanish.)  Linear term: sum_{a != m} tau(y_a) = 0 for all m gives tau(y_m) = T for all m and T = 5T, so (C1).
 Quadratic term: sum_{a<b, a,b != m} <y_a,y_b> = (1/2)(<s,s> - Q) + q_m with Q = sum_a <y_a,y_a>, and sum_m q_m = Q - <s,s>;
 so all five vanish iff all q_m vanish.  Cubic and quartic terms are (C3), (C4).  QED
 Polarisation of (C2_m) on the linear space L':  2<y_m,y'_m> - <s(Y),y'_m> - <s(Y'),y_m> = 0 for Y, Y' in L'.   (C2pol)
 Normalised cubic for s(Y) = 0 (ID3: e_3 of five numbers of sum 0 without x_m equals p_3/3 + x_m p_2/2 - x_m^3):
   T_m(Y) = tau(P3)/3 + tau(y_m Psi)/2 - tau(y_m^3),  Psi := sum_a y_a^2, P3 := sum_a y_a^3;  sum_m T_m = (2/3) tau(P3).
 So on doubly centred Y, (C3_m for all m) implies   (C3*_m)  tau(y_m^3) = (1/2) tau(y_m Psi)  for all m.

### S3 Set-up: q, d, N, K
 Let L' be strongly level, S := s(L') inside V, q := dim S <= 3, N := {Z in L' : s(Z) = 0}, d := dim N; dim L' = q + d.
 Facts about the nondegenerate 3-dim quadratic space V:
  (Q1) a totally isotropic subspace has dim <= 1;  (Q2) non-proportional isotropic v, v' have <v,v'> != 0;
  (Q3) three pairwise non-proportional isotropic vectors are linearly independent (if v3 = a v1 + b v2 then
       0 = <v3,v3> = 2ab<v1,v2>);  (Q4) v != 0 isotropic, x isotropic or 0, <v,x> = 0  =>  x in C v.
 LEMMA N. For each m, {z_m : Z in N} is 0 ("inactive") or an isotropic line C v_m ("active").  Hence there are linear
 forms l_m on N (l_m not == 0 for m active) with Z = sum_{m active} l_m(Z) v_m e_m^T, and l = (l_m) embeds N into
   K := { l in C^{Act} : sum_m l_m v_m = 0 }.
 Proof. On N, q_m(Z) = <z_m,z_m>, so the projection is totally isotropic; (Q1).  QED
 Let k = number of active columns, g = number of distinct lines among C v_m (m active), generators normalised to be
 equal on equal lines. By (Q2),(Q3): rank{v_m} = min(g,3), dim K = k - min(g,3).  A line occurring on exactly one
 active column when g <= 3 forces l_m == 0 on K (independence), contradicting activity. So:
   g = 1: N = v (x) Lambda, Lambda a space of vectors l in C^5 with sum l = 0;
   g = 2: two classes M1 (line v), M2 (line v') of sizes >= 2: (2,2) [k = 4, dim K = 2] or (2,3) [k = 5, dim K = 3];
   g >= 3: dim K = k - 3 <= 2, with equality only for k = 5, and then N = K and the multiplicity pattern of the five lines
           is (2,1,1,1) or (1,1,1,1,1) (patterns (3,1,1) and (2,2,1) contain a singleton line among g = 3).

### S4 LEMMA A: dim N <= 2, and dim N = 2 only in types I-IV
 Power sums of an isotropic v != 0 in V (Newton with e_1 = e_2 = 0): tau(v^3) = 3 e_3(v), tau(v^4) = -4 e_4(v), and
 the entries of v are the roots of x^4 - e_3 x + e_4.  Hence (P-a) tau(v^4) = 0 => v has a zero entry and tau(v^3) != 0;
 (P-b) tau(v^3) = 0 => v = c (1,i,-1,-i) in some order of the rows (c != 0), and tau(v^4) = 4c^4 != 0.
 (A1) g = 1, N = v (x) Lambda.  (C3_m): tau(v^3) e_3(l without l_m) = 0;  (C4_m): -6 tau(v^4) prod_{a != m} l_a = 0.
   If tau(v^3) != 0: e_3(l minus l_m) = e_3 - l_m e_2 - l_m^3 (sum l = 0), sum over m gives 5e_3 - p_3 = 2 e_3 (p_3 = 3 e_3), so
   e_3 == 0 and l_m (l_m^2 + e_2) == 0 on Lambda; so every active l_m satisfies l_m^2 = -e_2, any two active forms are
   equal up to sign, all coordinates are multiples of one form: dim Lambda <= 1.
   If tau(v^4) != 0: for every m some l_a (a != m) vanishes identically on Lambda; taking m, then m = a, gives two
   coordinates a != b vanishing identically: Lambda lies in the sum-zero vectors on 3 columns, dim <= 2.
   By (P-a) one of the two cases holds: dim N <= 2.  If dim N = 2: tau(v^3) = 0, so (P-b) and
   TYPE I:  N = chi_1 (x) Lambda_M,  Lambda_M = sum-zero vectors supported on a 3-set M of columns (after a row permutation).
 (G23) LEMMA. Let v, v' be non-proportional isotropic, columns a, b, c1, c2, c3, and
   Z(mu,nu) = mu v (e_a - e_b)^T + v' nu^T, nu supported on {c1,c2,c3}, sum nu = 0. Then (direct expansion, ID4)
     T_a + T_b = 2 tau(v'^3) nu1 nu2 nu3,    [Z^(a)] = 6 mu nu1 nu2 nu3 tau(v v'^3),    [Z^(c1)] = -mu^2 nu2 nu3 [v,v,v',v'].
   No linear space P of such Z with (C3), (C4) has mu nu1 nu2 nu3 not == 0 on P.
   Proof. T_a + T_b == 0 gives tau(v'^3) = 0, so WLOG v' = chi_1 (P-b). [Z^(a)] == 0 gives <v,chi_3> = 0, so v = c chi_3
   (S0), c != 0. Then [v,v,v',v'] = c^2 [chi_3,chi_3,chi_1,chi_1] = 8c^2 (ID5) and [Z^(c1)] = -8c^2 mu^2 nu2 nu3 not == 0.  QED
 (A2) g = 2.  (2,2): dim N <= 2, and dim N = 2 means N = K:
   TYPE II:  N = { mu v (e_a - e_b)^T + mu' v' (e_c - e_d)^T },  fifth column inactive.
   (2,3): N inside K = {Z(mu,nu)} (3-dim) with all five columns active, i.e. mu not == 0 and each nu_i not == 0 on N.
   By (G23) with P = N this is impossible -- for dim N = 3 AND for dim N = 2 (this is "TYPE III", it does not exist).
 (A3) g >= 3: dim N <= 2 by S3, and dim N = 2 gives TYPE IV: N = ker[v_1..v_5], pattern (2,1,1,1) or (1^5).
 Summary: d <= 2; d = 2 => N is of type I, II or IV (IV is excluded in S6).

### S5 LEMMA B: the isometries B_m (uses C2 only)
 Fix a linear section sigma -> Y(sigma) in L' of s (sigma in S); write Y(sigma)_m = A_m sigma (A_m : S -> V linear),
 sum_m A_m = inclusion iota, and B_m := 2A_m - iota.
  (B1) <B_m sigma, B_m sigma'> = <sigma,sigma'> on S   [(C2_m) on Y(sigma): <A_m sigma,A_m sigma> = <sigma,A_m sigma>];
  (B2) sum_m B_m = -3 iota;
  (B3) <z_m, B_m sigma> = 0 for all Z in N, sigma in S   [(C2pol) with Y = Y(sigma), Y' = Z].
 Consequences:
  (B-i)  q = 3 => N = 0.  [B_m is an isometry of the nondegenerate V, so bijective; z_m perp V.]
  (B-ii) q = 2 and N != 0 => S = u^perp for an isotropic u != 0 (u in S).  [If S is nondegenerate, B_m(S) is a
         nondegenerate plane, its orthogonal line is non-isotropic, and z_m is isotropic in it: z_m = 0 for all m.]
  (B-iii) in case (B-ii) put b_m := B_m u. Then b_m is isotropic or 0, sum_m b_m = -3u, and b_m in C v_m for every
         active column m of N  [(B1), (B2), (B3) and (Q4)].  For Y = t Y(u) + Z, Z in N:
              y_m = t (b_m + u)/2 + z_m,     s(Y) = t u.
 So dim L' >= 4 forces (q,d) = (2,2) (as q <= 3, d <= 2, q = 3 => d = 0), with S = u^perp and N of type I, II or IV.

### S6 TYPE IV does not exist (uses C3 on N only)
 Isotropic lines of V: C chi_3 and C v(th), v(th) := chi_1 + th chi_2 - (th^2/2) chi_3 (S0: 8pr + 4q^2 = 0).
 The S_4-orbit of C chi_3 consists of 6 lines (the 24 orderings of (1,i,-1,-i) modulo multiplication by i^k), so for a configuration of at
 most 5 lines a row permutation makes all of them of the form C v(th_m); normalise v_m = v(th_m).   (ID6):
   v(th)^2 = -th^3 chi_1 + (1 + th^4/4) chi_2 + 2 th chi_3,     tau(v(th)^3) = 3 th (4 + th^4),
   Psi(l) = sum_a l_a^2 v_a^2 = A chi_2 + 2B chi_3 - C chi_1,  A = sum l_a^2 (1 + th_a^4/4), B = sum l_a^2 th_a, C = sum l_a^2 th_a^3,
   (1/2) tau(v(x) Psi) = G(x) := 4B + 2xA + x^2 C.
 (C3*_m) on N, divided by l_m (not == 0):     G(th_m)(l) = 3 th_m (4 + th_m^4) l_m^2   on N, for all m.        (+)
 Pattern (2,1,1,1): lines th_1 (columns a,b), th_c, th_d, th_e distinct; N = span(e_a - e_b, n), l = mu(e_a - e_b) + kappa n.
   In (+) for m = c the right side has no mu^2 term; the mu^2 coefficient of the left side is
   f(th_c), f(x) := 2 th_1^3 x^2 + (4 + th_1^4) x + 8 th_1. So f has three distinct roots th_c, th_d, th_e: f == 0, i.e.
   th_1 = 0 and 4 + th_1^4 = 0. Contradiction.
 Pattern (1^5): N = { l_m = g(th_m)/om'(th_m) : g = alpha + beta x }, om = prod (x - th_a)  (partial fractions; dim 2).
   Write G(x) = G_1(x) alpha^2 + G_2(x) alpha beta + G_3(x) beta^2 (deg_x G_i <= 2) and c_m := 3 th_m (4 + th_m^4)/om'(th_m)^2.
   (+) says G_1(th_m) = c_m, G_2(th_m) = 2 th_m c_m, G_3(th_m) = th_m^2 c_m. So G_2 - 2xG_1 (deg <= 3) and G_3 - x^2 G_1
   (deg <= 4) vanish at 5 points, hence identically; so G_1 = c_0 is constant, G = c_0 (alpha + beta x)^2, i.e.
        4B = c_0 alpha^2,  A = c_0 alpha beta,  C = c_0 beta^2,  and  c_m = c_0 for all m.
   c_0 = 0: th_m are the five roots of x^5 + 4x; om' = 5x^4 + 4 equals 4 at 0 and -16 at the others; the alpha beta
     coefficient of C is 2 sum th^4/om'(th)^2 = 2*4*(-4)/256 = -1/8 != 0. Contradiction.
   c_0 != 0: all th_m (4 + th_m^4) != 0 and 1/om'(th_m)^2 = c_0/(3 th_m (4 + th_m^4)), so A = (c_0/12) sum g(th_a)^2/th_a,
     whose alpha beta coefficient is (c_0/12)*2*5 = (5/6) c_0 != c_0. Contradiction.   QED

### S7 TYPE II: classification and exclusion (uses C3, C4 on N; C2, C3 for the exclusion)
 N = { mu v (e_a - e_b)^T + mu' v' (e_c - e_d)^T }, column e inactive. On N (ID4):
   T_a = mu mu'^2 tau(v v'^2),   T_c = mu^2 mu' tau(v^2 v'),   [Z^(e)] = mu^2 mu'^2 [v,v,v',v'],
 so  tau(v v'^2) = tau(v^2 v') = 0 and [v,v,v',v'] = 0.
 (II-a) Then v, v' have a common zero entry; after a row permutation and rescaling v = zeta, v' = conj(zeta).
   Proof. WLOG v = v(t), v' = v(u), t != u (S6). (ID7): tau(v(t) v(u)^2) = 4 E(t,u), E(t,u) = 2u + t + t u^4/4 + t^2 u^3/2;
   with a = t+u, b = tu:  E(t,u) + E(u,t) = (a/4)(12 + a^2 b - b^2),  E(t,u) - E(u,t) = ((u-t)/4)(4 + a^2 b + b^2),
   [v(t),v(t),v(u),v(u)] = 2(a^2 + 2b)^2 - (3/2)(b^2 - 4)^2.
   So 4 + a^2 b + b^2 = 0 and a(12 + a^2 b - b^2) = 0. If a = 0: b^2 = -4 and the bracket is -32 - 96 = -128 != 0. So
   12 + a^2 b - b^2 = 0, whence b^2 = 4, a^2 b = -8: (a,b) in {(2,-2), (-2,-2), (2i,2), (-2i,2)}. And (ID7)
   v(th)_k = -(i^{3k}/2)(th^2 - 2 i^{-k} th - 2 i^{-2k}), so v(th) has a zero in row k iff th^2 - a_k th + b_k = 0 with
   (a_k,b_k) = (2,-2), (-2i,2), (-2,-2), (2i,2) for k = 0,1,2,3: t, u are the two roots of one of these quadratics.
   The isotropic vectors with a zero in row 3 are the multiples of zeta and conj(zeta).  QED
 (II-b) (q,d) = (2,2) with N of type II is impossible.
   Proof. By (B-iii) b_a = be_a v, b_b = be_b v (and b_c, b_d in C v'). For Y = t Y(u) + Z in L':
   y_a = t(b_a+u)/2 + mu v, y_b = t(b_b+u)/2 - mu v, y_c = t(b_c+u)/2 + mu' v', y_d = t(b_d+u)/2 - mu' v'.
   Deleting the inactive column e: T_e(Y) = sum of tau over the 4 triples of {a,b,c,d}; its t mu'^2 coefficient comes from
   {a,c,d} and {b,c,d}:  -tau(v'^2 (b_a + b_b + 2u))/2 = -tau(v'^2 u) - ((be_a+be_b)/2) tau(v'^2 v) = -<u, v'^2>.
   So <u,v'^2> = 0 and symmetrically <u,v^2> = 0. With v = zeta, v' = conj(zeta): v^2 = v', v'^2 = v, so u is orthogonal
   to zeta, conj(zeta) and (1,1,1,1): u = c(1,1,1,-3), <u,u> = 12c^2 != 0. But u is isotropic, u != 0. Contradiction. QED

### S8 TYPE I excluded (uses C2, C3, C4)
 N = chi_1 (x) Lambda_M, M = {1,2,3}; columns 4, 5 inactive; (B-iii): b_m = be_m chi_1 (m in M), b_4, b_5 isotropic or 0,
   b_4 + b_5 = -3u - (be_1+be_2+be_3) chi_1.    Y = t Y(u) + chi_1 x^T (x in Lambda_M):
   y_m = (x_m + t be_m/2) chi_1 + t u/2 (m in M),   y_4 = t(b_4+u)/2,   y_5 = t(b_5+u)/2.
 Step 1 (C3). The part of T_m(Y) of degree 1 in t and 2 in x (ID4; tau(chi_1^2 z) = <chi_2,z>, tau(chi_3) = 0):
     T_4: (1/2) e_2(x) (2<chi_2,u> + <chi_2,b_5>),   T_5: (1/2) e_2(x) (2<chi_2,u> + <chi_2,b_4>),
     T_1: (1/2) x_2 x_3 (2<chi_2,u> + <chi_2,b_4+b_5>) = -(1/2) x_2 x_3 <chi_2,u>.
   Hence <chi_2,u> = <chi_2,b_4> = <chi_2,b_5> = 0, and (S0) u, b_4, b_5 lie in C chi_1 u C chi_3.
 (ID8) for y_i = p_i chi_1 + r_i chi_3:  [y_1,y_2,y_3,y_4] = -24 (p_1p_2p_3p_4 + r_1r_2r_3r_4) + 8 sum_{|P|=2} p_P r_{P^c}.
 Step 2: u = c chi_3 (c != 0) is impossible. Write b_4 = pi_4 chi_1 + rho_4 chi_3 (pi_4 rho_4 = 0). Deleting column 5:
   p_m = x_m + t be_m/2, r_m = tc/2 (m in M), p_4 = t pi_4/2, r_4 = t(rho_4 + c)/2. The x_1x_2x_3 t coefficient of (ID8)
   is -12 pi_4, so pi_4 = 0; then the bracket is t^2 c (rho_4 + c)(2 e_2(p_1,p_2,p_3) - (3/2) t^2 c^2), whose x-quadratic
   part 2 t^2 c (rho_4 + c) e_2(x) must vanish: rho_4 = -c, b_4 = -c chi_3. Likewise b_5 = -c chi_3. Then the chi_3
   coefficient of b_4 + b_5 = -3u - (sum be) chi_1 reads -2c = -3c. Contradiction.
 Step 3: u = c chi_1 (c != 0) forces Y(u) in chi_1 (x) C^M. Deleting column 5: r_1 = r_2 = r_3 = 0, so (ID8) gives
   -24 p_1p_2p_3 p_4 with p_4 = t(pi_4 + c)/2: pi_4 = -c != 0, so rho_4 = 0, b_4 = -u, y_4 = 0. Likewise y_5 = 0.
   So R := C Y(u) (+) N = chi_1 (x) C^M (3-dim) lies in L' (this is the "R3" space; it is strongly level).
 Step 4: no fourth vector. L' = R (+) C Y_4 with s(Y_4) in S \ C u, S = u^perp = span(chi_1, chi_2). Columns eta_m of Y_4.
   (C2pol) with Y' = chi_1 x^T (x in C^M), using <s(Y_4),chi_1> = 0:  (2x_m - sum x) <eta_m,chi_1> = 0 for all x, m;
   so <eta_m,chi_1> = 0, eta_m = pi_m chi_1 + ka_m chi_2 for all m; scale so that sum ka_m = 1 (it is != 0).
   (C2_m) on Y_4: 4 ka_m^2 = 4 ka_m, so ka_m in {0,1}: exactly one column m_0 has ka = 1. Subtract an element of R to
   get pi_m = 0 for m in M. Then for Y = chi_1 x^T + t Y_4 (x in C^M), since tau(chi_1^3) = tau(chi_1 chi_2^2) =
   tau(chi_2^3) = 0 and tau(chi_1^2 chi_2) = 4, only triples containing m_0 contribute to T, each with 4t x (products of
   the chi_1-coefficients of the other two columns):
     m_0 in M, say m_0 = 1:  T_4(Y) = 4t (x_2 x_3 + t pi_5 (x_2 + x_3))  not == 0;
     m_0 = 4 (or 5):          T_5(Y) = 4t (x_1x_2 + x_1x_3 + x_2x_3)       not == 0.
   Contradiction with (C3).  QED

### S9 Conclusion
 LEMMA SL: a strongly level space L' of 4x5 matrices has dim <= 3.  Proof: dim L' = q + d, q <= 3, d <= 2 (S4);
 q = 3 => d = 0 (B-i); so dim L' >= 4 would force (q,d) = (2,2), S = u^perp (B-ii), N of type I, II or IV (S4),
 excluded by S8, S7, S6.  QED
 THEOREM FL: a level space L of 5x5 matrices containing a full free row or column has dim L <= 7.
 Proof: transpose/permute to F_5 inside L; Prop R: dim L = 4 + dim L' <= 7.  QED   (Sharp: L080, ex1-3, families, R3.)
 Where P_4/P_5 enters: (C4) is used in S4 (A1 second case, G23), S7 (II-a, only to discard a = 0), S8 Steps 2, 3.

### S10 The finitely many polynomial identities (checked at random complex points to 3e-14, test2.py/test3.py, and
### EXACTLY (Gaussian-rational arithmetic, all differences exactly 0) at random points, test5_exact.py/test6_exact.py)
 ID1  Laplace expansion of the 5x5 permanent along a row.
 ID2  perm(J_4 + cZ) for column-sum-zero Z (S2): coefficients -2 sum <z_a,z_b>, 2 sum tau(z_a z_b z_c), bracket; linear
      coefficient 6 (sum of entries) for arbitrary Z.
 ID3  five numbers with sum 0: e_3(without x_m) = p_3/3 + x_m p_2/2 - x_m^3 (= e_3 - x_m e_2 - x_m^3), p_3 = 3 e_3;
      four numbers with e_1 = e_2 = 0: p_3 = 3 e_3, p_4 = -4 e_4.
 ID4  multilinear expansions of T_m and of the bracket on the explicit families (G23, type II, type I Step 1, Step 4);
      [v,v',v',v'] = -6 tau(v v'^3) and [v,v,v,v] = -6 tau(v^4), [v,v,v',v'] = -6 tau(v^2 v'^2) + 2<v,v'>^2 for isotropic v, v'.
 ID5  character table: chi_a chi_b = chi_{a+b}, tau(chi_a) = 4[4 | a]; [chi_3,chi_3,chi_1,chi_1] = 8.
 ID6  v(th) = chi_1 + th chi_2 - (th^2/2) chi_3: <v(t),v(u)> = -2(t-u)^2, v(th)^2, tau(v(th)^3) = 3th(4 + th^4), Psi, G.
 ID7  tau(v(t)v(u)^2) = 4E(t,u), the two factorisations of E(t,u) +- E(u,t), [v(t),v(t),v(u),v(u)] in a, b,
      v(th)_k = -(i^{3k}/2)(th^2 - 2 i^{-k} th - 2 i^{-2k}).
 ID8  bracket on span(chi_1, chi_3).
 ID9  type IV: f(x) (mu^2 coefficient of G), partial-fraction kernel sum_m th_m^j g(th_m)/om'(th_m) = 0 (j <= 2, deg g <= 1),
      values om'(0) = 4, om'(th) = -16 on th^4 = -4, and sum th^4/om'^2 = -1/16.
 Non-identity ingredients for Lean: (Q1)-(Q4) in V; "polynomial == 0 on a linear space => coefficients" (replace by
 evaluation at explicit witnesses); the two WLOGs (row permutation moving <= 5 isotropic lines off C chi_3; (P-b));
 polynomial-interpolation step in S6 (degree <= 4 polynomial with 5 roots).

### S11 Remarks for a Lean formalisation
 - The S_4 "WLOG all lines finite" is needed only in S6 (<= 5 lines, 6 lines in the orbit of C chi_3). In S7 it can be
   replaced by a direct check of the point at infinity: if v' = chi_3 and v = v(t) then tau(v v'^2) = <v,chi_2> = 4t = 0,
   so v = chi_1, and [chi_1,chi_1,chi_3,chi_3] = 8 != 0 (checked).
 - Every "not == 0 on a linear space" above has an explicit witness (e.g. x = (1,1,-2) for x1x2x3 and e_2(x) on Lambda_M;
   a point with all coordinates nonzero exists on N as soon as all columns are active), so coefficient extraction can be
   done by evaluating at finitely many explicit elements of L' (linear combinations with t, mu in {0, 1, -1, 2}).
 - S5 needs only bilinear algebra in V (dim 3); S4 (A1) needs "l_m^2 = l_n^2 as forms => l_m = +- l_n".
 - Corollary used by the team (zeros (b)): if L is level and L_r := L cap {row r = 0} is strongly level, then dim L <= 7
   (the row-r projection of a level space has dim <= 4, since a row of J + t equal to 0 gives perm = 0 != 120).
 - Independent data: the only one-vector extensions of the type II plane found by a calibrated search are
   N + C(1,1,1,-3)^T e_4^T (ex1), of the type I plane chi_1 (x) C^M (R3); so numerically ex1' and R3' are the only
   3-dim strongly level spaces with d = 2 (up to symmetry).


## DI5 (verifyfl, round 2, start 15:49, budget 90 min): the defect inequality at e = 1  --  what is proved

### DI5.0 Set-up (e = 1)
 L' = linear space of 4x5 matrices Y (columns y_1..y_5 in C^4), C(Y)_j := perm(J_4 + Y^(j)); "defect line C m" means
 C(Y) - 24*1 = thetahat(Y) m for all Y in L' (m != 0, sum m = 0; thetahat a polynomial on L'); then L' is level and
 C(L') = C m (or 0). kappa(Y) m = column sums of Y (kappa linear). Neutral column: m_j = 0. Target: dim L' <= 4.
 Notation from the blueprint S0: tau, <,>, V, isotropic, chi_a, zeta_0 := (1,w,w^2,0), bracket.  New notation on C^4:
   Q(d) := tau(d)^2 - <d,d> = 2 e_2(d),   eps(d,d') := tau(d)tau(d') - <d,d'>  (polar form, nondegenerate on C^4),
   E(d)_i := e_2(d without d_i) = e_2(d) - tau(d) d_i + d_i^2,   E(d,d') := its polarisation (E(d,d) = E(d)),
   F_v(d) := <v,E(d)> = tau(v d^2) - tau(d) tau(v d)  for v in V.
   If Q(z) = 0 then E(z) = z^2 - tau(z) z lies in V; if eps(d,z) = 0 then E(d,z) = d o z - (tau(d) z + tau(z) d)/2 lies in V.
   For Q(z) = 0:  E(z) = 0 iff z is a multiple of a unit vector e_i (z_i in {0, tau(z)} for all i).

### DI5.1 LEMMA EQ (any m; rigorous; checked on all 24 e = 1 example spaces, strong-level error <= 3e-13, di_test1.py)
 Let L' have defect line C m and let pi be a permutation of the columns with m o pi != m. Then
   L'^pi := {Y in L' : Y o pi = Y}  is STRONGLY level, hence dim L'^pi <= 3 (Lemma SL).
 In particular for a != b with m_a != m_b:  {Y in L' : y_a = y_b} is strongly level, so
   dim L' <= 3 + rank(Y -> y_a - y_b) for every such pair (this is rows' Lemma TC(iii) for arbitrary m).
 Proof. C_j(Y o pi) = C_{pi(j)}(Y). If Y o pi = Y then thetahat(cY)(m_j - m_{pi(j)}) = 0 for all j, c; so thetahat(cY) = 0. QED
 Formula for the defect function (multilinearity in columns a, b; {k,l,n} the other columns):
   (m_b - m_a) thetahat(Y) = C_b - C_a = perm[ y_a - y_b, 1+y_k, 1+y_l, 1+y_n ].
 General e: the same proof gives  C(L'^pi) inside C(L')^pi (the pi-invariant vectors of C(L')); for a transposition (a b)
 with C(L') not inside {c_a = c_b}:  e(L'^{(ab)}) <= e - 1.   (Induction step discussed in DI5.6.)

### DI5.2 Two-column defect line m = e_1 - e_2: SYMMETRISED NORMAL FORM (rigorous; identities to 5e-15, di_test3.py)
 Write u := (y_1+y_2)/2, d := (y_1-y_2)/2, Ybar := [u,u,y_3,y_4,y_5].  By multilinearity and symmetry of perm in columns:
   C_1 + C_2 = 2 perm(J_4 + [u,y_3,y_4,y_5]),     C_2 - C_1 = 2 perm[d, 1+y_3, 1+y_4, 1+y_5],
   C_j = perm(J_4 + [u,u,y_k,y_l]) - perm[d,d,1+y_k,1+y_l]   (j = 3,4,5; {k,l} = {3,4,5} minus j),
   perm[d,d,1+a,1+b] = 4 e_2(d) + 2 <a+b, E(d)> + perm[d,d,a,b]     (a, b in V).
 Hence: L' has defect line inside C(e_1 - e_2)  <=>  for all Y in L':
   (i)  the 4x4 matrix [u,y_3,y_4,y_5] is level;        (ii) perm(J_4 + [u,u,y_k,y_l]) = 24 + perm[d,d,1+y_k,1+y_l].
 By degree (columns u, y_3, y_4, y_5 are in V; tau(d) = kappa; s = 2u + y_3 + y_4 + y_5; qbar_j, Tbar_j, brackets of Ybar as in S2):
   (C2')  qbar_3 = qbar_4 = qbar_5 = 0,   qbar_1 := <u,u> - <s,u> = Q(d);
   (C3')  Tbar_1 = 0 (triples of u,y_3,y_4,y_5),   Tbar_j = <y_k + y_l, E(d)>  (j = 3,4,5);
   (C4')  [u,y_3,y_4,y_5] = 0,   [u,u,y_k,y_l] = perm[d,d,y_k,y_l].
 Objects: zeta := {z : z(e_1-e_2)^T in L'};  L'' := {d = 0} (strongly level, <= 3);  D := {d(Y)};  Lbar := {Ybar} = L'/zeta;
   S := s(L'), q := dim S;  Nbar := {Ybar in Lbar : s = 0};      dim L' = q + dim Nbar + dim zeta = dim L'' + dim D.
 LEMMA Z (rigorous). (Z1) Q = 0 on zeta (so dim zeta <= 2) and eps(D, zeta) = 0; Q descends to a quadratic form Qbar on Lbar.
   (Z2) for all Y in L', z, z' in zeta, k != l in {3,4,5}:  <y_k, E(z,z')> = 0,  <y_k + y_l, E(d(Y),z)> = 0,
        perm[z,z',y_k,y_l] = 0,  perm[d(Y),z,y_k,y_l] = 0.
   Proof. (Z1): (C2') on z(e_1-e_2)^T; polarise qbar_1 between Y and z(e_1-e_2)^T. (Z2): Y and Y + t z(e_1-e_2)^T have the same
   Ybar; compare (C3'), (C4') and take the t and t^2 coefficients; the three pair sums give each <y_k, E(z)> = 0; polarise in z. QED
 LEMMA LAG (rigorous). Let zeta be a 2-dim Q-isotropic subspace of C^4 and E_zeta := span{E(z,z')} (inside V). Then
   (a) dim E_zeta >= 2;   (b) E_zeta is not orthogonal to any vector of chi_1 type (4 distinct 4th roots, tau(n^3) = 0).
   Proof. zeta cap V = C z_0 (z_0 isotropic in V, a 2-dim totally isotropic subspace of V does not exist) and zeta = C z_0 + C z_1,
   tau(z_1) = 1, <z_1,z_1> = 1, <z_0,z_1> = 0. E(z_0) = z_0^2 != 0, E(z_0,z_1) = z_0 o (z_1 - 1/2), E(z_1) = z_1 o (z_1 - 1).
   (a) If E(z_0,z_1) = lam z_0^2 then z_1 = 1/2 + lam z_0 on supp z_0; supp z_0 has >= 3 elements; if it has 4, tau(z_1) = 2,
   contradiction; if 3, then (mod z_0) z_1 = (1/2,1/2,1/2,-1/2) on a zero-row z_0 = zeta_0 and E(z_1) = (-1,-1,-1,3)/4 is not
   proportional to z_0^2.  (b) WLOG n = chi_1. <chi_1, z_0^2> = 0 forces z_0 = chi_1 or chi_3 (for z_0 = v(t): 8t). With
   z_1 = 1/4 + p chi_1 + q chi_2 + r chi_3 (8pr + 4q^2 = 3/4): z_0 = chi_1 gives r = 0 and <chi_1,E(z_0,z_1)> = 4q = 0,
   contradicting q^2 = 3/16; z_0 = chi_3 gives <chi_1, E(z_0,z_1)> = -1.  QED   [3000 random Lagrangians: never orthogonal.]
 LEMMA NB (neutral isometries; rigorous, = blueprint S5 for the three neutral columns). For a section sigma -> Ybar(sigma) of s
   the maps B_j = 2A_j - iota (j = 3,4,5) are isometric on S, and <z_j, B_j sigma> = 0 for Zbar in Nbar; columns 3,4,5 of Nbar
   lie in isotropic lines C v_j or vanish. Hence: q = 3, or q = 2 with S nondegenerate  ==>  Nbar = 0 (then u = 0 too).
   Also <B sigma, u_Z> = 2 eps(d(sigma), d(Z)) for B := 2A - iota (the u-column), and <u_Z,u_Z> = Qbar(Zbar).

### DI5.3 THEOREM TC5 (RIGOROUS): a 4x5 space L' with defect line inside C(e_a - e_b) has dim L' <= 4.
 Equivalently: there is no (5,1) space with a two-column defect line, i.e. no 8-dim level space with a deletable row whose defect line is
 e_a - e_b.  Ingredients: Lemma SL and its classification (blueprint S4-S8), the normal form DI5.2, Lemmas Z, LAG, NB, and one exact
 resultant identity (F1).  All closed forms were checked numerically (di_test3/4/5) and the theorem was tested against 22 example spaces.
 Proof (a = 1, b = 2). Suppose dim L' = 5.
 (P1) dim zeta = 2 is impossible. Then D inside zeta^perp = zeta, so L' = L'' (+) zeta (x) (e_1-e_2)^T with dim L'' = 3.
   By (Z2) and LAG(a) all neutral columns of L' lie in the line C n := E_zeta^perp cap V (or vanish).
   n non-isotropic (<n,n> = 1), c := number of neutral columns not identically 0 on L'': (C2') gives y_j = <s,n> n on those,
   so L'' is parametrised by u (c != 1) or by (u, lam) with <u,n> = 0 (c = 1), and qbar_1 = 0 reads
     c = 0: <u,u> = 0;  c = 1: <u,u> = 0 on n^perp;  c = 2: <u,u> = 4<u,n>^2;  c = 3: <u,u> = 3<u,n>^2,
   each a NONDEGENERATE quadratic form on its 3- or 2-dim space: dim L'' <= 1, 2, 1, 1. Contradiction.
   n isotropic and c >= 1: (C2') gives <s,n> = 0, so <u,n> = 0 and qbar_1 = -<u,u> = 0: u in C n; L'' = n (x) Lam, 3-dim strongly level with all
   columns on one isotropic line: (q,d) = (1,2), so tau(n^3) = 0 (S4 A1), n of chi_1 type, contradicting LAG(b).
 (P2) So dim zeta <= 1 and q + dim Nbar >= 4. By NB: q = 3 or S nondegenerate give Nbar = 0. So q <= 2 and dim Nbar >= 2.
 (P3) dim Nbar = 3 is impossible. Then Nbar = {[u,u,l_3 v_3,l_4 v_4,l_5 v_5] : l in C^3}, 2u = -sum l_j v_j, and (C3'), (C4')
   for the deletion of one u-column (no d involved) read, with g_jk = <v_j,v_k>:
     sum_{j != k} l_j^2 l_k tau(v_j^2 v_k) + l_3 l_4 l_5 tau(v_3 v_4 v_5) = 0,
     l_3 l_4 l_5 sum_j l_j ( 3 tau(v_j^2 v_k v_l) - g_jk g_jl ) = 0.
   Three equal lines: tau(v^3) = 0 and 3 tau(v^4) = 0, impossible (P-b). Two equal (v,v,v'): tau(v^3) = tau(v^2 v') = tau(v v'^2) = 0
   gives (v,v') = (chi_1,chi_3) up to S_4, and the coefficient of l_5 is 3 tau(chi_1^2 chi_3^2) - <chi_1,chi_3>^2 = 12 - 16.
   Three distinct lines: every pair satisfies tau(v v'^2) = tau(v^2 v') = 0; by S7 (II-a) such pairs are (a = 0, b^2 = -4)
   ["antipodal": th' = -th, th^4 = -4] or zero-row pairs [th in {+-1 +- sqrt 3} u i{+-1 +- sqrt 3}]; every th occurs in exactly
   one such pair (|th| = sqrt 2 resp. sqrt 3 +- 1), so three pairwise related lines do not exist.
 (P4) Hence dim Nbar = 2, q = 2, S = n_0^perp (n_0 isotropic), dim zeta = 1 (zeta = C z).  Let k be the number of active neutral
   columns of Nbar and N' the preimage of Nbar in L' (dim 3), D_N := d(N') (contains z).
   (N-a) k = 2, one line v: Tbar_1 = -tau(v^3) l_3 l_4 (l_3+l_4)/2 gives tau(v^3) = 0, v = chi_1; u in C chi_1, Qbar = 0 on Nbar, so D_N
     is Q-isotropic; (C3') gives <chi_1, E(d)> = 0 on D_N. dim D_N = 2 contradicts LAG(b); dim D_N = 1 makes Nbar a DC strongly level
     plane chi_1 (x) {(-(l_3+l_4)/2, same, l_3, l_4, 0)} with four active columns, contradicting S4 (A1).
   (N-b) k = 2, lines v_3 != v_4: tau(v_3^2 v_4) = tau(v_3 v_4^2) = 0 (Tbar_1), Qbar = l_3 l_4 g/2 has rank 2, so d : N' -> zeta^perp is
     bijective and (C3') for the deletions 3, 4 gives  F_{v_j}(d) = (tau(v_j^3)/4) l_j(d)^2  on the hyperplane zeta^perp (j = 3,4).
     Antipodal pair = (chi_1,chi_3): F_{chi_1} = 8(d_1 d_2 - d_0 d_3) (character coordinates) is nondegenerate on C^4 and would
     vanish on a 3-dim subspace. Zero-row pair (zeta_0, conj zeta_0): F_{zeta_0} has rank 3 with radical C h, h = (1,1,1,-1); its
     restriction to zeta^perp has rank <= 1, so h lies in zeta^perp and in ker l_3; likewise in ker l_4; ker l_3 cap ker l_4 = C z, so
     z = h; but (Z2) needs perm[z,z,v_3,v_4] = 0 and perm[h,h,zeta_0,conj zeta_0] = 6.
   (c1) k = 3, one line v: Nbar is a plane in {(l_3,l_4,l_5)}; [u,z_3,z_4,z_5] = 3 tau(v^4)(l_3+l_4+l_5) l_3 l_4 l_5. If tau(v^4) = 0 then
     tau(v^3) != 0 and Tbar_1 = tau(v^3) e_3(-sig/2,l_3,l_4,l_5) = -(tau(v^3)/2)((l_3+l_4)(l_4+l_5)(l_5+l_3) - l_3 l_4 l_5), an
     irreducible cubic (it contains no line), which cannot vanish on a plane. So Nbar = v (x) Lam_{345}, u = 0, tau(v^3) = 0, v = chi_1.
     Qbar = 0 on Nbar, <chi_1,E(d)> = 0 on D_N, so D_N = zeta by LAG(b) and Nbar = N'' lies in L''.  Now run S8 on the exact
     deletion of a u-column (Ybar = t Ybar(n_0) + chi_1 x^T, b := B n_0, b_j = be_j chi_1, 2b = -3n_0 - (sum be) chi_1):
     Tbar_1: (1/2) e_2(x)(2<chi_2,n_0> + <chi_2,b>) = (1/4) e_2(x) <chi_2,n_0> = 0, so n_0 in C chi_1 u C chi_3.
     n_0 = c chi_3: the bracket of the u-deletion has x_3x_4x_5-coefficient 6 t (sum be), so sum be = 0, and then its
       x-quadratic part is -t^2 c^2 e_2(x) != 0.     n_0 = c chi_1: the bracket is -24 p_u p_3 p_4 p_5, so u(n_0) = 0 and
       Rbar := chi_1 (x) C^{345} lies in Lbar; Qbar = 0 on Rbar and LAG(b) give d = zeta on it: R := chi_1 (x) C^{345} lies in L''.
     Fourth vector Y_4 (s(Y_4) = chi_2 + pi chi_1, columns u_4 = pi_u chi_1 + ka_u chi_2, eta_j = pi_j chi_1 + ka_j chi_2 by (C2pol)
     on the neutral columns and s in S): (C2') ka_j in {0,1}; x^2 t part of Tbar_1 gives ka_j = -ka_u; with 2ka_u + sum ka_j = 1:
     ka_j = 1, ka_u = -1; Tbar_1 = 8 t^2 pi_u (x_3+x_4+x_5) gives pi_u = 0; then the bracket of the u-deletion is
     [-t chi_2, x_3 chi_1 + t chi_2, x_4 chi_1 + t chi_2, x_5 chi_1 + t chi_2] = -24 t^4 != 0.  Contradiction.
   (c3) k = 3, three distinct lines: if E(z) != 0 the three lines lie in the plane E(z)^perp (Z2), which contains at most two
     isotropic lines. If z = e_i: (Z2) gives d'(Z) (= d with the i-th entry removed; sum 0) orthogonal to v_3, v_4, v_5, which span V,
     so d(N') = zeta and Nbar = N'' is a DC strongly level plane with three distinct lines: types I, II have <= 2 (S4).
   (c2) k = 3, lines (v,v,v') on columns (3,4,5), v != v'. Put a := l_3+l_4, b := l_5, t_3 := tau(v^3), t_21 := tau(v^2 v'),
     t_12 := tau(v v'^2), t_03 := tau(v'^3), g := <v,v'> != 0; u = -(a v + b v')/2, Qbar = a b g/2 on Nbar. Closed forms (checked, di_test4.py):
       -2 Tbar_1 = l_3 l_4 (a t_3 - b t_21) + a b (a t_21 + b t_12),      [u,z_3,z_4,z_5] = l_3 l_4 b ( 3 tau(v^3 v') a + (3 tau(v^2 v'^2) - g^2) b ),
       Tbar_5 = a tau(u^2 v) + 2 l_3 l_4 tau(u v^2),   Tbar_3 = l_4 tau(u^2 v) + b tau(u^2 v') + 2 l_4 b tau(u v v'),   Tbar_4 = same with l_3,
       tau(u^2 v) = (a^2 t_3 + 2ab t_21 + b^2 t_12)/4, tau(u^2 v') = (a^2 t_21 + 2ab t_12 + b^2 t_03)/4, tau(u v^2) = -(a t_3 + b t_21)/2,
       tau(u v v') = -(a t_21 + b t_12)/2;     (C3'):  Tbar_5 = a F_v(d),  Tbar_3 = l_4 F_v(d) + b F_{v'}(d),  Tbar_4 = l_3 F_v(d) + b F_{v'}(d).
     (c2-i) a, b independent on Nbar. Then Qbar has rank 2 and d : N' -> zeta^perp is bijective, so F_v, F_{v'} are quadratic forms in N'.
       If l_3 - l_4 is not == 0: Tbar_4 - Tbar_3 gives F_v = (a^2 t_3 - 2ab t_21 - 3 b^2 t_12)/4; with Tbar_5 = a F_v:
       l_3 l_4 (a t_3 + b t_21) = a b (a t_21 + b t_12); with Tbar_1 = 0: 2 a l_3 l_4 t_3 = 0, so t_3 = 0, v = chi_1; then
       (a^2 - l_3 l_4) t_21 + a b t_12 = 0 with a^2 - l_3 l_4 = (3a^2 + (l_3-l_4)^2)/4 forces t_12 = 0 and (t_21 = 0 or (l_3-l_4)^2 = -3a^2);
       t_12 = tau(chi_1 v'^2) = 0 with t_21 = <chi_2,v'> != 0 is impossible (v' = v(th): 8 th), so t_21 = 0, v' = chi_3, F_{chi_1} = 0 on zeta^perp.
       If l_3 = l_4 on Nbar: F_v = b(a t_21 + b t_12)/4 and b F_{v'} = a^3 t_3/8 - a^2 b t_21/8 + b^3 t_03/4, so t_3 = 0; Tbar_1 = 0 gives
       (3/4) a^2 b t_21 + a b^2 t_12 = 0, so t_21 = t_12 = 0, v' = chi_3, F_{chi_1} = 0 on zeta^perp.  Both contradict the nondegeneracy of F_{chi_1}.
     (c2-ii) Nbar = {l_3 + l_4 = c l_5}, c != 0 (coordinates b, l_3 - l_4): the same two steps give t_3 = 0, then Tbar_1 = 0 gives
       t_21 = t_12 = 0, so (v,v') = (chi_1,chi_3), and the bracket of the u-deletion is l_3 l_4 b^2 (3 tau(chi_1^2 chi_3^2) - 16) = -4 l_3 l_4 b^2. Contradiction.
     (c2-iii) Nbar = {l_3 + l_4 = 0} = {[-b v'/2, -b v'/2, l v, -l v, b v']}: Tbar_1 = 0 and the u-bracket give t_21 = 0 and 3 tau(v^2 v'^2) = g^2
       (equivalently [v,v,v',v'] = 0); Qbar = 0 on Nbar, so D_N is Q-isotropic; (C3') gives F_v(d) = -(3/4) t_12 b^2, F_{v'}(d) = (t_03/4) b^2.
       - D_N = zeta: Nbar = N'' would be a DC strongly level plane of type III (classes {3,4} and {1,2,5}): excluded by (G23).
       - D_N Lagrangian. For generic Z in N' (l, b != 0), (Z2) gives v, v' orthogonal to E(z) and to E(d(Z),z) (pairs (3,5), (4,5): sum and
         difference), hence to E(d,z) for all d in D_N.
         (F1) [EXACT] distinct isotropic lines with tau(v^2 v') = 0 and [v,v,v',v'] = 0 form a ZERO-ROW PAIR. Proof: v = v(t), v' = v(u) (S6);
           tau(v^2 v') = 4((t^3/2) u^2 + (1 + t^4/4) u + 2t) =: 4 E_t(u),  [v,v,v',v'] = 2(t^2+4tu+u^2)^2 - (3/2)(t^2u^2-4)^2 =: P_t(u), and
               Res_u(E_t, P_t) = -(3/256) (t^8 - 56 t^4 + 16)^3        (exact rational arithmetic, verifyfl/di_res_exact.py);
           t^8 - 56t^4 + 16 = (t^4 - 8t^2 + 4)(t^4 + 8t^2 + 4) is the product of the four zero-row quadratics of S7, and it is 16 times the
           discriminant of E_t; the leading coefficients t^3/2 and 2 - (3/2)t^4 have no common zero. So t is a zero-row parameter, E_t has a
           double root u, and u is the zero-row partner of t (which is a solution by S7).  QED
         So WLOG {v,v'} = {zeta_0, conj zeta_0} (zero row 3) and E(z) lies in V cap span(v,v')^perp = C (1,1,1,-3).
         tau(z) = 0: E(z) = z^2, so z = rho (+-1,+-1,+-1,+-i sqrt 3) with sum 0: impossible unless z = 0.
         tau(z) = 1: (F2) z is one of e_0, e_1, e_2, e_3, h/2 (h = (1,1,1,-1)).  [w := z - 1/2 has w_i^2 = 1/4 + lam n_i, n = (1,1,1,-3),
           sum w = -1: with w_i = eps_i rho (i < 3), k = sum eps_i: (1 + k rho)^2 = 1 - 3 rho^2, so rho = 0 (z = h/2) or rho^2 = 1/4 (z = e_i).]
           z = e_i: D_N cap V = C z_0 with z_0(i) = 0 (eps(e_i,z_0) = 0), E(z_0,e_i) = -z_0/2, so v, v' are orthogonal to the isotropic z_0,
             hence both in C z_0. Contradiction.
           z = h/2: (Z2) requires perm[z,z,y_3,y_5] = (l b/4) perm[h,h,zeta_0,conj zeta_0] = (3/2) l b = 0. Contradiction.
         [Independent numerical confirmation: di_resid.py (LM on the 14 necessary conditions: no zero in 1782 starts, calibrated) and
          di_enum.py (enumeration: the pairs of (F1) are the 8 ordered zero-row pairs; (F2) has exactly the 5 solutions).]
 QED  (every branch by hand, except the polynomial identity for the resultant in (F1), which is exact computer arithmetic)
 What the proof does NOT exclude (as it must not): rows' exact7b has (q, dim Nbar, dim zeta) = (2,1,1), my examples below have (1,1,2) and
 (1,2,1), LM hits have (3,0,0) and (3,0,1). Case count for dim 5: dim zeta <= 1 (P1), dim Nbar <= 2 (P3), Nbar != 0 => q <= 2 (NB): only (2,2,1).

### DI5.4 New exact example (third kind) and a false conjecture
 L'_3 := span{ uh (e_0-e_3)^T, z_1 (e_0-e_3)^T, ub e_1^T, ub e_4^T },  uh = (1,w,0,w^2), ub = (1,w^2,0,w), z_1 = (1,1,-1,1)/2
 is a (4,1) space with m = e_0 - e_3 (level error 1e-13, defect singular values (244, 0, 0)); L(L'_3) is a 7-dim level space (1.9e-13).
 It contains rows' M_2 (so M_2 DOES extend to dimension 4), has kappa != 0, no split free row, zeta Lagrangian, and ker kappa is NOT
 strongly level. [In 22 of the 24 numerical (4,1) spaces ker kappa IS a 3-dim strongly level space of type (3,0) and the space
 contains e_i m^T; the conjecture "kappa != 0 => ker kappa strongly level" (which would settle the case kappa != 0 by SL) is FALSE.]
 Derivation: zeta = span(uh, z_1) is Lagrangian with E_zeta = span(ub, (1,1,-3,1)); neutral columns must be orthogonal to E_zeta:
 the isotropic line C ub; the quartic conditions perm[z,z',ub,ub] = 0 hold (common zero row / sum of cube roots).

 Fourth exact example (found while testing the proof): L'_4 := chi_1 (x) C^{345} (+) C e_i (e_1-e_2)^T is a (4,1) space with m = e_1 - e_2
 (level error 4e-14), split, with (q, dim Nbar, dim zeta) = (1,2,1): its Nbar is the type-I plane chi_1 (x) Lam_{345} of case (c1); the proof
 of (c1) shows that such a space cannot have q = 2.  Calibrated extension test with m fixed (di_test6.py): for rows' exact7b, L'_3 and L'_4
 a random 3-dim subspace re-extends (8/8 each) and the 4-dim space itself never does (0/14 each)  [numerical].

### DI5.5 Numerics for this section (verifyfl/di_*.py)
 di_test1: Lemma EQ on the 24 e = 1 examples (all pairs with m_a != m_b): strongly level to 3e-13.
 di_test2: census: 22/24 have kappa != 0, ker kappa strongly level (3,0), split free row; 1 has kappa = 0 ((q,d) = (2,2), m two-column).
 di_test3: identities of DI5.2 (5e-15), third-kind example, LAG on 3000 random Lagrangians.
 di_ext: the candidate "type II plane (+) h(e_1-e_2)^T" of (N-b) is NOT a defect-line space (residual 145), as the proof says.
 di_test5 [error-catching test asked for by the coordinator]: on all 22 available two-column e = 1 spaces (rows' exact7b and seed t6, M_2,
   third kind, 18 LM hits of di_gr) the symmetrised equations (C2')-(C4'), Lemma Z, Lemma NB hold (<= 2e-9, LM-limited) and every space is of a
   type the proof allows: (q, dim Nbar, dim zeta) in {(3,0,0), (3,0,1), (2,1,1), (1,1,2), (0,0,2)}; none is excluded. (Three LM hits show a
   rank-tolerance artefact in dim L'' + dim D: singular values 1e-6..1e-8 of Y -> y_a - y_b.)
 di_test4: all closed forms used in (P3), (P4) (to 3e-14).   di_res_exact: the exact resultant of (F1).   di_resid, di_enum: numerical
   confirmation of the last sub-branch (now also proved by hand).
 di_gr [NUMERICAL ONLY]: LM on Gr(k,17) with m = e_0 - e_1 fixed: k = 3: 9/10 converge, all (q, dim Nbar, dim zeta) = (3,0,0);
   k = 4: 9/61 converge: types (3,0,1) (7x) and (2,1,1) (2x) -- exactly the types the proof leaves room for (plus the exact (1,1,2));
   k = 5: 0/84 (calibrated by the 15% rate at k = 4: moderate evidence).

### DI5.6 General m (e = 1) and e = 2, 3: what carries over, what does not (assessment; nothing here is a theorem unless marked)
 RIGOROUS for every m: (G1) Lemma EQ.  (G2) every neutral column j (m_j = 0) has an exact C2: q_j = 0 on ALL of L' (also when kappa != 0),
   so B_j is isometric on S and the neutral columns of N' = {s = 0} are isotropic lines, 0 if q = 3 or S is a nondegenerate plane (Lemma NB);
   the deletion of a neutral column is a 4x4 level space.  (G3) symmetrisation in ANY pair (a,b), u = (y_a+y_b)/2, d = (y_a-y_b)/2:
     perm(J_4 + [u,y_k,y_l,y_n]) = 24 + thetahat (m_a+m_b)/2,   perm[d,1+y_k,1+y_l,1+y_n] = thetahat (m_b-m_a)/2,
     perm(J_4 + [u,u,y_k,y_l]) - perm[d,d,1+y_k,1+y_l] = 24 + thetahat m_j      (j not in {a,b}).
 What is special about m = e_a - e_b and fails otherwise: (1) thetahat drops out of all equations except one (three neutral columns and
   m_a + m_b = 0), so the symmetrised space has corrections QUADRATIC in d only; for general m the symmetrised space keeps the linear
   term thetahat m^sym and one must carry the unknown forms theta_2, theta_3, theta_4;  (2) zeta_ab = {z : z(e_a-e_b)^T in L'} is at most
   1-dim (an isotropic line of V: e_2(z) = 0 by levelness and 6 tau(z)(e_b - e_a) in C m) unless m is proportional to e_a - e_b, so the mechanism "Lagrangian zeta" (third-kind example)
   is specific to two-column m;  (3) the examples with general m (22 of 24) all contain the split free row e_i m^T, have kappa != 0 and
   ker kappa strongly level of type (3,0) -- for them the natural route is rows' 3-row formulation (their (E1), (E2)), not this one.
 Split case, two exact remarks (rigorous, not yet used): if e_i m^T =: Y_1 is in L' then (S1) thetahat is AFFINE along Y_1:
   thetahat(Y + t Y_1) = thetahat(Y) + t mu(Y3), where Y3 = the three rows of Y other than i and D_i(Y3) m = mu(Y3) m (row i enters
   C(Y) linearly; mu(0) = -6);  (S2) polarising p_2 between Y in L' and Y_1 gives m_j (s_i(Y) - 2 Y_ij) in C m, i.e. row i of every Y in L'
   is constant on supp(m) modulo C m.  Observed (23 split examples incl. L'_4): ker kappa is strongly level; by (S1) this is equivalent to
   "the rational section Y_0 -> Y_0 - (thetahat(Y_0)/mu(Y3_0)) Y_1 of strongly level points is linear on ker kappa"; a proof would settle the
   split case by Lemma SL (dim L' = 1 + dim ker kappa <= 4).
 FALSE shortcut (DI5.4): "kappa != 0 => ker kappa strongly level".   OPEN: is every e = 1 space either split (contains e_i m^T) or
   two-column?  [All known (4,1) spaces are: 22 numerical split ones, and the two-column ones: rows' exact7b, t6, t22 (approx.), my third kind,
   and the 9 LM hits of di_gr.]  If yes, TC5 plus the split case (rows' claim "3-row projection has dim <= 3") would give (DI_5) at e = 1.
 e = 2, 3: Lemma EQ becomes  C(L'^pi) inside C(L')^pi; for a transposition with C(L') not inside {c_a = c_b} the fixed space
   L'_ab = {y_a = y_b} has defect dimension <= e - 1.  So an INDUCTION ON e would follow from a bound on D_ab = {y_a - y_b}:
     dim L' = dim L'_ab + dim D_ab <= (e - 1) + 3 + dim D_ab   (given (DI_5) for e - 1).
   The needed statement "dim D_ab <= 1 for a suitable pair" is FALSE as stated already at e = 1 (third-kind example: dim L'' = 2, dim D = 2;
   rows' exact7b: dim L'' = 3, dim D = 1): the correct invariant is the pair, and what TC5's proof establishes is exactly the trade-off
     dim L'' + dim D <= 4   via   dim L' = q + dim Nbar + dim zeta   with   [dim zeta = 2 => dim L'' <= 2],  [q = 3 or S nondegenerate => Nbar = 0],
     dim Nbar <= 2,  and the exclusion of (2,2,1).
   A uniform argument would have to prove this trade-off for the symmetrised pair (Lbar, Qbar) with defect C cap {c_a = c_b}; the quadratic
   stage (isometries of the neutral columns, Lagrangian zeta) is uniform, the cubic/quartic stage is not (it uses the explicit conic).
   I do not see a uniform proof; for e = 2, 3 the realistic plan is: (a) neutral columns exist in all known examples (rows: C(L') = sum-zero
   vectors on 3 columns for (5,2)), use (G2) there; (b) prove first the case where C(L') is spanned by two-column vectors.

## DI5-R3 (verifyfl, round 3, start 17:38, budget 90 min): the SPLIT case of (DI_5), and what it says about (5,1), (6,2), (7,3)

### R3.0 The symmetric form (one line, used everywhere below)
 Per(r_1,...,r_5) := permanent of the 5x5 matrix with rows r_1..r_5 (symmetric, 5-linear). For a 4x5 matrix Y with rows y^1..y^4 put
 l_i := 1 + y^i. Laplace expansion along the fifth row:   <w, C(Y)> = Per(l_1, l_2, l_3, l_4, w)   for every w in C^5.
 So "L' has defect space C" means:  Per(l_1,..,l_4,w) = 24 tau(w) + <w, c(Y)>,  c(Y) := C(Y) - 24*1 in C, for all Y in L', w.
 Since a single row enters linearly:  C(Y + t e_i u^T) = C(Y) + t D_i(Y) u,  where D_i(Y) is the SYMMETRIC 5x5 matrix with
 <w, D_i(Y) u> = Per(l_1,.., u (slot i),.., l_4, w)  (it depends only on the three rows of Y other than i; D_i(0) = 6(J - I)), and
 C(Y) = D_i(Y) l_i.   gamma(Y) := vector of column sums of Y;  c(Y) = -6 gamma(Y) + O(Y^2), so gamma(Y) lies in C.

### R3.1 THEOREM SPLIT (e = 1; RIGOROUS, three lines).  Let L' be a 4x5 space with defect line C m containing e_i m^T, and <m,m> != 0. Then
      thetahat(Y) = kappa(Y) mu(Y)   for all Y in L'     (mu(Y) := the eigenvalue: D_i(Y) m = mu(Y) m,  mu(0) = -6),
 hence ker kappa = {Y in L' : column sums 0} is STRONGLY LEVEL, dim ker kappa <= 3 (Lemma SL) and dim L' <= 4.
 In particular: NO (5,1) SPACE IS SPLIT WITH A NON-ISOTROPIC DEFECT LINE (and none contains a (5,1)-subspace of that kind).
 Proof. (1) Y + t e_i m^T is in L', so C(Y) + t D_i(Y) m is in 24*1 + C m for all t: D_i(Y) m = mu(Y) m.
 (2) thetahat(Y) <m,m> = <m, C(Y)> = <m, D_i(Y) l_i> = <D_i(Y) m, l_i> = mu(Y) <m, y^i>   (symmetry of D_i; <m,1> = 0).
 (3) The parts of degree 1 in Y of (2): -6 kappa(Y) <m,m> = -6 <m, y^i>. So <m,y^i> = kappa(Y) <m,m>, and (2) becomes
     thetahat(Y) <m,m> = mu(Y) kappa(Y) <m,m>.  QED
 Checked on all 24 split example spaces (rows' 22, t22, my L'_4): |thetahat - kappa mu| <= 1.4e-6 (LM-limited), r3_test1.py.
 Remarks. (a) This proves the round-2 observation "ker kappa is strongly level in all split examples" and rows' claim "the 3-row
 projection has dim <= 3" (dim L' = 1 + dim of the 3-row projection) for <m,m> != 0.  (b) For ISOTROPIC m (<m,m> = 0, at least three
 non-neutral columns) (2)-(3) only give <m,y^i> = 0; the statement is OPEN there (see R3.4).

### R3.2 THEOREM FS ("fully split in one row"; any e; RIGOROUS).  Let L' be a 4x5 level space with defect space C = C(L'). Assume
 (i) e_i (x) C lies in L' for some row i (the single-row part of row i is all of C; it is always inside C by rows' (H1)), and
 (ii) the form <,> is nondegenerate on C.  Then  c(Y) = D_i(Y) gamma(Y)  for all Y in L';  so ker gamma is strongly level and
      dim L' <= 3 + rank(gamma) <= 3 + e:   (DI_5) HOLDS FOR L'.  In particular (6,2) and (7,3) spaces of this kind do not exist.
 Proof. By R3.0, D_i(Y) u lies in C for u in C. For u in C: <u, c(Y)> = <u, D_i(Y) l_i> = <D_i(Y) u, y^i>. Degree 1 in Y:
 <u, gamma(Y)> = <u, y^i> for all u in C; applying this to u' = D_i(Y) u in C: <u, c(Y)> = <D_i(Y) u, gamma(Y)> = <u, D_i(Y) gamma(Y)>;
 both c(Y) and D_i(Y) gamma(Y) lie in C and <,> is nondegenerate there. Lemma SL bounds ker gamma.  QED
 Check: rows' seed_d5_e2_t0 and t2 are fully split in one row (single-row dims [2,0,0,0], [0,0,2,0]) and their ker gamma is strongly level
 (2e-14). Most (5,2) and (6,3) examples are split over SEVERAL rows or not at all (single-row dims [0,1,1,0], [0,0,1,0], [0,0,0,0]); ker gamma
 is still strongly level of dim 3 in 10 of 12 of them, but NOT in clm_p4_d5_defect2_s9 (C degenerate, rank 1) and clm_p4_d6_defect3_s3
 (rank gamma = 2 < e = 3) [numerical, r3_test2.py]. So "ker gamma strongly level" is not a general law, and the several-rows case needs the
 cross pairings <y^i, u'> (u' in the single-row part of another row), which the argument does not control.

### R3.2' THEOREM TS (split over TWO rows, e = 2; RIGOROUS; identities checked on 6 examples to 1e-13, r3_test3.py)
 Let L' be a 4x5 level space with 2-dim defect space C = C u (+) C u', where e_i u^T and e_k u'^T lie in L' for two rows i != k, and
 <u,u> != 0 != <u',u'>.  Then <u,u'> = 0, and with the linear forms X(Y) := <y^i, u'>, X'(Y) := <y^k, u> and
 D_ik(Y)(u,u') := (Per(.., u (slot i), .., u' (slot k), .., e_j))_j  (in C; it depends on the other two rows; D_ik(0)(u,u') = 4 u o u'):
       c(Y) = X(Y) X'(Y) D_ik(Y)(u,u') / (<u,u><u',u'>)      for all Y with gamma(Y) = 0.
 Consequently ker gamma cap ker X and ker gamma cap ker X' are strongly level, dim ker gamma <= 4 and dim L' <= 6 (= e + 4, one more than
 (DI_5)); a (6,2) space of this kind is K (+) C e_i u^T (+) C e_k u'^T with K = ker gamma 4-dim, X X' not == 0 on K, and K contains
 the 3-dim strongly level hyperplanes {X = 0}, {X' = 0}.   [(6,2) of this kind: NOT excluded.]
 Proof. The tt' coefficient of c(t e_i u^T + t' e_k u'^T) is 2(2 u o u' - <u,u'> 1), which must lie in C inside 1^perp: <u,u'> = 0.
 All of D_i(Y)u, D_k(Y)u', D_ik(Y)(u,u') lie in C (coefficients of c(Y + t e_i u^T + t' e_k u'^T)). By the symmetry of Per:
   <u,c(Y)> = <y^i, D_i(Y)u>,  <u',c(Y)> = <y^k, D_k(Y)u'>,  <u', D_i(Y)u> = <y^k, D_ik(Y)(u,u')>,  <u, D_k(Y)u'> = <y^i, D_ik(Y)(u,u')>.
 Degree 1 of the first two: <y^i,u> = <u,gamma(Y)>, <y^k,u'> = <u',gamma(Y)>. On ker gamma, writing D_i u = a u + a' u', D_k u' = b u + b' u',
 D_ik(u,u') = d u + d' u':  <u,c> = a' X,  a' <u',u'> = d X',  <u',c> = b X',  b <u,u> = d' X.  QED
 In the five nondegenerate two-row examples one of X, X' vanishes identically on ker gamma (so ker gamma is strongly level, dim 3).
 (I expect the same bookkeeping for C distributed over three or four rows, with a product of cross pairings; not written out.)

### R3.3 LEMMA HYP (RIGOROUS): how the dichotomy would finish (5,1).
 (a) Every 4-dim subspace H of a (5,1) space L' is a (4,1) space with the same defect line (e(H) <= 1, and e(H) = 0 is excluded by SL).
 (b) L' contains at most four lines C e_i m^T; a generic hyperplane H of L' contains none of them. Hence:
     if every (4,1) space with defect line C m contains some e_i m^T ["dichotomy at dimension 4" for this m], then no (5,1) space with
     defect line C m exists.   (No hypothesis on <m,m>; R3.1 is not needed for this implication.)
 (c) With R3.1 and TC5: a (5,1) space with non-isotropic, non-two-column m would be NON-SPLIT, and all of its 4-dim subspaces would be
     non-split (4,1) spaces with that m.  So (DI_5) at e = 1 is equivalent to:
       (NS4)  there is no 5-dim space all of whose hyperplanes are non-split (4,1) spaces;   sufficient: every (4,1) space with a
              non-two-column defect line is split.
 Evidence for the sufficient statement [NUMERICAL]: rows' 22 general-m (4,1) spaces are split; my searches with m fixed (r3_gr.py):
 m = (1,2,-3,0,0): (3,1) 6/12 hits, 5 of them NON-split; (4,1) 3/40 hits, ALL split; m = (1,2,3,-1,-5) (no neutral column): (3,1) 1/12
 (non-split), (4,1) 0/39.  So non-split spaces are common in dimension 3 and unseen in dimension 4 for non-two-column m.

### R3.4 The isotropic defect line: Theorem SPLIT is sharp, the split case stays open there
 For <m,m> = 0 (sum m = 0 and sum m_j^2 = 0; e.g. (1,w,w^2,0,0), (1,i,-1,-i,0)) step (2) of R3.1 degenerates to <m,y^i> = 0 and gives
 no information on thetahat.  The CONCLUSION of R3.1 is then FALSE in low dimension [NUMERICAL, 1e-14, verifyfl/r3_iso.py, saved in
 r3_iso_counterexample.npy]: for m = (1,w,w^2,0,0) there are 2-dim spaces span(e_3 m^T, Y_0) with defect line C m, kappa(Y_0) = 0 and
 thetahat(Y_0) = 0.27 + 0.27i != 0 (D m = mu m to 4e-15).  So "ker kappa strongly level" needs <m,m> != 0.
 Split (5,1) with isotropic m: NOT excluded by proof.  Numerically (r3_split_search.py: start from e_3 m^T, add one vector at a time, m fixed):
 m = (1,w,w^2,0,0) and (1,i,-1,-i,0) reach dimension 4 easily (2/10, 4/10, 8/10, 1/10 at the last step, ker kappa strongly level there) and
 never dimension 5 (0/10 in each of 4 runs); the non-isotropic control (1,2,-3,0,0) behaves the same (dimension 4 reached, 5 never).
 NEW KIND OF (4,1) SPACE [NUMERICAL, independent check: the 7-dim 5x5 space L(L') is level to 1.7e-13; verifyfl/r3_iso3.py, r3_iso4.py,
 data r3_iso4_s0.npy]: for m = (1,w,w^2,0,0) there are SPLIT (4,1) spaces whose ker kappa (3-dim, type (q,d) = (2,1)) is NOT strongly level
 (strong-level error 3.4, 4.5); 8 of 33 random split (2,1) spaces with this m have a non-strongly-level ker kappa and several of them
 extend to dimension 3 and 4.  None of the two saved 4-dim spaces extends to dimension 5 (0/60 starts each, m fixed; the same search
 succeeds at the steps 2 -> 3 -> 4 in 4/12 .. 10/12 of the starts).  Broader search (r3_iso5.py: 12 different split (4,1) spaces for three
 isotropic m, incl. (1,i,-1,-i,0) and a 4-entry one): 0 extensions to dimension 5 in 300 starts.  So the isotropic split case is a genuinely
 different family, and still no (5,1) space appears in it.
 Remark: for isotropic m the 5x5 space L(L') contains e_5 m^T as well (m lies in {1,m}^perp), a structural difference not yet exploited.

### R3.5 Where (DI_5) at e = 1 stands after rounds 2 and 3
 PROVED: no (5,1) space (i) with two-column defect line (TC5); (ii) containing a single-row element, if <m,m> != 0 (R3.1).
 By rows' (H1) every single-row element of L' is a multiple of some e_i m^T; so a (5,1) space with <m,m> != 0 has NO single-row elements,
 and by R3.3 none of its 4-dim subspaces has one.
 REMAINING (exact statements, each sufficient together with the above):
   (NS4')  every (4,1) space with non-two-column defect line contains some e_i m^T          [=> no (5,1) with that m, by R3.3(b)];
   (K4)    in every (4,1) space with non-two-column, NON-ISOTROPIC m and kappa != 0, ker kappa is strongly level
           [=> no (5,1) with kappa != 0: all hyperplanes of the 4-dim ker kappa would be strongly level, hence ker kappa itself];
   (K4')   a (4,1) space with kappa == 0 has a two-column defect line   [the kappa == 0 half];
   (ISO)   the isotropic case of the split statement.
 [NUMERICAL] all 35 known (4,1) spaces with non-two-column m (rows' 22 + 13 found here with m fixed: (1,2,-3,0,0) 8x, (1,1,-2,0,0) 4x,
 (1,2,-4,1,0) 1x) satisfy (NS4') and (K4), with ker kappa strongly level of type (3,0) (q = 3); for m without neutral column, (1,2,3,-1,-5),
 no (4,1) space was found at all (0/39).  (K4) is FALSE for two-column m (third-kind example), for isotropic m (R3.4, dimension 4) and in dimension 1 for general m
 (a single matrix with zero column sums and p_2, p_3, p_4 proportional to a given m: 9 conditions on 15 parameters), so any proof must use
 dim >= 4, m not two-column and <m,m> != 0.
 Column-centred spaces (kappa == 0) with a good defect line [NUMERICAL, r3_z.py, r3_z5.py]: spaces with ALL column sums zero and defect line
 exactly C m exist in dimension 1, 2 and 3 for good m ((1,2,-3,0,0): 10/13, 18/30, 4/10 of the LM hits are genuinely not strongly level),
 so "kappa == 0 => strongly level or two-column" is false below dimension 4.  But the four such 3-dim spaces tested (q = 3) are DEAD ENDS:
 no extension to dimension 4 with defect line C m (0/56 starts; the same extension search re-extends random 3-dim subspaces of known (4,1)
 spaces 8/8).  This is the mechanism one would have to prove: in a (5,1) space every 3-dim subspace of ker kappa would be an extendable
 column-centred space with defect in C m, hence (if such spaces are always strongly level) ker kappa would be strongly level of dim >= 4.
   (E3)  a column-centred 3-dim space with defect line exactly C m (m good) lies in no 4-dim space with defect line C m
         [=> no (5,1) with good m; together with TC5 and (ISO) this is (DI_5) at e = 1].
 Quadratic normal form in the observed situation (rigorous, short; not yet a proof of (NS4')): let L' be a (4,1) space, kappa != 0, with
 K := ker kappa strongly level and s(K) = V. Then L' = K (+) C Z with s(Z) = 0, kappa(Z) = 1, Z vanishing on the neutral columns, and
     Z = sum_{j in P} m_j h_j e_j^T,   tau(h_j) = 1, <h_j,h_j> = 1 (Q(h_j) = 0),   sum_{j in P} m_j h_j = 0,   h_j = 1/4 - 2 B_j f,
 where B_j in O(V) are the isometries of K (blueprint S5), f in V is fixed with <f,f> = 3/16, and theta_2(Z) = 0.
 [Lemma B' polarised between K and Z gives <B_j sigma, z_j^0> = -2 m_j phi(sigma) with ONE linear form phi; its norm identity
  16 m_j^2 <f,f> = 3 m_j^2 - 4 theta_2(Z) m_j for two different values of m_j gives <f,f> = 3/16 and theta_2(Z) = 0.]
 L' is split iff all h_j equal one unit vector e_i. For |P| = 3 the three h_j are collinear points of the quadric {tau = 1, <h,h> = 1}:
 either they coincide (Z = h m^T of rank one) or they lie on an isotropic affine line. Deciding these with the cubic cross conditions is
 the natural next computation (same size as one branch of TC5).

### R3.6 stage3's family N2 (NOTES-stage3, (N2-h)): what the tools of rounds 2-3 give
 (N2-h) produces, given (N2-unit), a TRANSPOSED (5,1) or (6,1) space L^j with explicit defect line eta (5 entries, indexed by the rows of L).
 It is excluded (i) by TC5 if eta = e_r - e_r' mod 1 (already noted by stage3); (ii) by R3.1 (transposed) if, after normalising sum eta = 0,
 <eta,eta> != 0 and L^j contains a single-COLUMN element with column vector eta in some column j' != j; (iii) by R3.3 + R3.1 if merely every
 4-dim subspace of L^j with defect contains such an element.  Whether (ii) holds for N2 is not decided by the data in section 18 of
 NOTES-stage3 (the known single-column elements Z^j e_j^T sit in the deletable column j itself); eta has two entries fixed by rho_a^j, rho_b^j
 and three by zeta(a_i), so generically it is neither two-column nor isotropic.  So N2 needs the non-split case of (5,1) -- i.e. (NS4')/(K4).

### R3.7 Numerics of this round (verifyfl/r3_*.py; every run <= 2 min CPU)
 r3_test1: thetahat = kappa mu and the three steps of R3.1 on 24 split examples.   r3_test2: e = 2, 3 examples (single-row parts, ker gamma).
 r3_look: structure of the split examples (ker kappa has column ranks (3,2), (2,1,2), (1,1,1), (2,1), ...: no uniform column shape).
 r3_gr, r3_gr2: Gr(k,17) searches with fixed general m (dimension 3: non-split common; dimension 4: 13 hits, all split).
 r3_split_search: climbing from e_3 m^T for isotropic and non-isotropic m.   r3_iso, r3_iso2-5: isotropic counterexamples and extension tests.
 r3_test3: pairing identities and the two-row formula of R3.2' on the e = 2 examples; FS formula c = D_i gamma on the two fully split ones (1e-15).
 r3_z, r3_z4, r3_z5: column-centred spaces with defect line C m (dimensions 1-4) and their extensions.

## DI5-R4 (round 4: the principal stratum; Theorem PR3; reformulation SL_m)

 Notation as in DI5 / DI5-R3. L' is a level 4 x 5 space with C(Y) = 24*1 + thetahat(Y) m (m != 0, sum m = 0), P = supp m, columns outside P
 are NEUTRAL (C_n == 24 on L'). c(Y) = kappa(Y) m are the column sums, s(Y) in V the row-sum vector (tau(s) = total sum = 0),
 y_j^0 := y_j - (kappa m_j/4) 1 in V the centred columns, b_j(Y) := 2 y_j^0 - s(Y) in V.  thetahat_2 = degree-2 part of thetahat,
 Theta its polar form.  sigma_k(X) = sum of the k x k subpermanents of a 4 x 4 matrix X, so perm(J+X) = 24 + 6 sigma_1 + 2 sigma_2 + sigma_3 + perm X,
   sigma_2(X) = sum_{a<b} (tau(x_a)tau(x_b) - <x_a,x_b>),
   sigma_3(X) = sum_{a<b<c} (tau_a tau_b tau_c - <x_a,x_b>tau_c - <x_a,x_c>tau_b - <x_b,x_c>tau_a + 2 tau(x_a x_b x_c)).

 R4.1 LEMMA QB (quadratic normal form WITH defect; rigorous, valid on all of L', any m).
   (a) sum_a <y_a,y_a> = <s,s> + kappa^2 <m,m>;
   (b) <b_j(Y), b_j(Y)> = <s,s> + 3 kappa^2 m_j^2 - 2 thetahat_2(Y) m_j   for every column j = 1..5.
   In particular for a neutral column n: b_n^* g = s^* g on L' (g = the form <,> on V), exactly as in Lemma B' of the blueprint.
   Proof. Degree 2 of C_j - 24 = thetahat m_j is 2 sigma_2(Y^(j)) = thetahat_2 m_j.  With sum c = 0:
   2 sum_{a<b != j} c_a c_b = kappa^2 (2 m_j^2 - <m,m>), 2 sum_{a<b != j} <y_a,y_b> = <s,s> - 2<s,y_j> + 2<y_j,y_j> - sum_a <y_a,y_a>.
   Summing the five equations over j gives (a) (the right side sums to 0); substituting (a) gives
   <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(thetahat_2/2) m_j, which is (b) after centring (<y_j,y_j> = <y_j^0,y_j^0> + kappa^2 m_j^2/4).  QED
   General defect space C (any e): the same computation gives sum_a <y_a,y_a> = <s,s> + <c,c> and
   <b_j,b_j> = <s,s> + 3 c_j(Y)^2 - 2 thetahat_2(Y)_j  (thetahat_2 now C-valued).

 R4.2 REFORMULATION (rigorous, trivial but it is the cleanest target).  Call a space COLUMN-CENTRED if all column sums vanish.
   (SL_m)  a column-centred 4 x 5 space whose deletion vectors lie in 24*1 + C m has dimension <= 3.
   (SL_0) is Lemma SL.  If L' is a (5,1) space with line C m then ker kappa is a column-centred space of dim >= 4 with defect in C m; so
       (SL_m) for every non-two-column m  ==>  (DI_5) at e = 1, split or not, isotropic or not   (with TC5 for two-column m).
   Equivalently (Lemma SL): there is no column-centred (4,1) space with non-two-column m.  (SL_m) is FALSE for two-column m [NUMERICAL examples:
   rows' seed_d4_e1_t6, my di_gr_k4_s100#3 and the three control hits of r4_z4.py are column-centred (4,1) spaces with m = e_a - e_b; by
   contrast all 42 stored (4,1) spaces with non-two-column m have kappa != 0 (r4_cc.py)], so a proof must use that m is not two-column.  This is exactly "Lemma SL with the extra form thetahat":
   by QB the quadratic stage reads b_j^* g = s^* g - 2 m_j thetahat_2 (five forms of rank <= 3 in the pencil s^*g + x thetahat_2).

 R4.3 THEOREM PS (principal stratum; rigorous, any m).  Let L' be a level space with defect in C m and suppose ker kappa contains a
   3-dim STRONGLY LEVEL subspace H with s(H) = V ("H principal"; this is the type (3,0) of Lemma SL, the only type seen in the 35 known
   (4,1) spaces with GOOD m, i.e. non-two-column and non-isotropic; for isotropic m, (4,1) spaces with ker kappa not strongly level exist, R3.4).  Let B_j := b_j o (s|_H)^{-1}, isometries of (V,g) (Lemma B'), and N := ker(s : L' -> V).  Then
   (a) L' = H (+) N, and there is an injective linear map f : N -> V with
          z_j = m_j ( (kappa(Z)/4) 1 - 2 B_j f_Z )   for all Z in N and all columns j   (so N is supported on the columns of P);
   (b) <f_Z,f_Z> = (3/16) kappa(Z)^2 and thetahat_2(Z) = 0 for Z in N;  sum_{j in P} m_j B_j f_Z = 0;
   (c) dim N <= 2, hence dim L' <= 5; and dim L' = 5 iff N = C Z (+) C Z_* with kappa(Z) = 1, kappa(Z_*) = 0, f_* := f_{Z_*} isotropic
       and <f_Z,f_*> = 0.  Then ker kappa = H (+) C Z_*, Z_* is doubly centred with isotropic columns z^*_j = -2 m_j B_j f_* (all nonzero
       for j in P), and thetahat_2(eta + t Z_*) = 4 t <f_*, s(eta)> is not identically 0 on ker kappa.
   Proof. s|_H is onto V, so L' = H (+) N.  Polarise QB(b) between Y_0 in H (sigma = s(Y_0), kappa = 0) and Z in N (s(Z) = 0):
   <B_j sigma, b_j(Z)> = -2 m_j Theta(Y_0,Z).  sigma -> Theta(Y_0(sigma),Z) is a linear form on V, = 2<f_Z,sigma> for a unique f_Z in V,
   linear in Z; as B_j is an isometry onto V this gives b_j(Z) = 2 z_j^0 = -4 m_j B_j f_Z, which is (a) (f_Z = 0 forces kappa = 0 by (b)
   and then Z = 0).  QB(b) for Z itself: 16 m_j^2 <f_Z,f_Z> = 3 kappa^2 m_j^2 - 2 thetahat_2(Z) m_j, i.e. (16<f_Z,f_Z> - 3 kappa^2) m_j =
   -2 thetahat_2(Z) for all j in P; m is not constant on P (sum m = 0), so both sides vanish: (b); the last relation is s(Z) = 0.
   (c): g restricted to f(N) is (3/16) kappa^2, of rank <= 1, and a totally isotropic subspace of the nondegenerate 3-dim (V,g) has
   dim <= 1; so dim f(N) <= 2, with equality only in the stated form.  Theta(eta, Z_*) = 2<f_*, s(eta)>.  QED
   [Check, r4_test1.py: on the 18 known split (4,1) spaces with principal ker kappa, Z = e_i m^T, the B_j are isometries (7e-14),
    <f,f> = 3/16 (5e-16) and (1/4)1 - 2 B_j f = e_i (2e-14).]
   So in the principal stratum everything is controlled by the plane N, "the N-problem":
     a 2-dim space N of matrices supported on the columns of P, zero row sums, column sums in C m (kappa not == 0), level with defect in C m,
     <y_j^0,y_j^0> = (3/4) kappa^2 m_j^2 on N, and every column map N -> V, Y -> y_j^0 (j in P) INJECTIVE.

 R4.4 LEMMA PR-RED (rigorous).  If every (4,1) space with line C m and principal ker kappa is split (contains some e_i m^T) ["principal (NS4')"],
   then no (5,1) space with line C m has a principal H in ker kappa.
   Proof. In such a (5,1), L' = H (+) C Z (+) C Z_* (PS).  For each t, H (+) C(Z + t Z_*) is a 4-dim level space with defect in C m and
   kappa != 0, hence not strongly level: a (4,1) space with principal ker kappa = H.  If it contains e_i m^T, then (kappa = 1, s = 0)
   e_i m^T = Z + t Z_*.  Two values of t with the same row i give Z_* = 0.  QED
   In the normal form: principal (NS4') says that h_j := (1/4)1 - 2 B_j f (tau(h_j) = 1, <h_j,h_j> = 1, sum m_j h_j = 0) is the SAME unit
   vector e_i for all j in P.

 R4.5 THEOREM PR3 (rigorous; uses only R4.1, R4.3 and the character table of Z/4).  Let m be non-isotropic with |supp m| = 3.
   Then no (5,1) space with defect line C m has a principal 3-dim strongly level subspace in ker kappa.
   [Equivalently: in a (5,1) space with such m, NO 3-dim subspace H of ker kappa with s(H) = V is strongly level.  Since every hyperplane
    of a (5,1) other than ker kappa is a (4,1) space (Lemma HYP) whose ker kappa is a hyperplane of the 4-dim ker kappa, this says:
    a (5,1) space with such m has no (4,1) hyperplane of the only kind known numerically.]
   Proof. P = {a,b,c}.  Suppose L' = H (+) C Z (+) C Z_* as in PS(c).
   (1) Z_* = chi_1 l^T up to a row permutation, l supported on P, all l_j != 0, sum l = 0.  Indeed z^*_a + z^*_b + z^*_c = 0 (s(Z_*) = 0)
       with all three isotropic gives <z^*_j,z^*_k> = 0, so they span a totally isotropic subspace: z^*_j = l_j v, v isotropic, l_j != 0.
       A neutral column n gives 24 = C_n(Z_*) = 24 + 2 sigma_2 + sigma_3 with sigma_2 = 0, sigma_3 = 2 l_a l_b l_c tau(v^3): tau(v^3) = 0.
       So p_1(v) = p_2(v) = p_3(v) = 0, the entries of v are the four roots of x^4 = const (Newton): v is a multiple of a row permutation
       of chi_1 = (1,i,-1,-i).  Row permutations preserve all hypotheses.
   (2) Z = h_0 m^T + chi_1 alpha^T with h_0 = (1/4)1 + beta chi_2, beta = +-sqrt(3)/4, alpha supported on P, sum alpha = 0.
       Indeed <z_j^0, z^*_j> = 4 m_j^2 <f_Z,f_*> = 0, so z_j^0 lies in chi_1^perp cap V = span(chi_1,chi_2): z_j^0 = m_j(alpha_j chi_1 +
       beta_j chi_2), and <z_j^0,z_j^0> = 4 m_j^2 beta_j^2 = (3/4) m_j^2 gives beta_j = +-sqrt(3)/4.  s(Z) = 0 gives sum m_j beta_j = 0;
       if the signs were not all equal this would read 2 m_j beta = 0 for one j in P.  So beta_j = beta for all j.
   (3) Hence N = { Y = kappa h_0 m^T + chi_1 lam^T : (kappa, lam) in N' }, N' a plane in C x W_P (W_P = zero-sum vectors on P) not contained
       in kappa = 0.  On the whole 3-dim family: <h_0,h_0> = 1, <h_0,chi_1> = 0, so <y_j,y_k> = kappa^2 m_j m_k (j != k in P), tau(y_j) = kappa m_j,
       and for a neutral column n: sigma_2 = 0, perm = 0, sigma_3 = 2 (tau(y_a y_b y_c) - kappa^3 e_3(m)).  With tau(h_0^3) = 5/8,
       tau(h_0^2 chi_1) = 0, tau(h_0 chi_1^2) = 4 beta, tau(chi_1^3) = 0:
           C_n(Y) - 24 = 2 kappa ( 4 beta Q_m(lam) - (3/8) e_3(m) kappa^2 ),   Q_m(lam) := m_a lam_b lam_c + m_b lam_a lam_c + m_c lam_a lam_b,
           C_a(Y) - 24 = -6 kappa m_a  (a in P)                                  [checked numerically, r4_pr3.py (1): 1e-14].
   (4) C_n == 24 on N and kappa is not identically 0 on N', so the quadratic form G = 4 beta Q_m(lam) - (3/8) e_3 kappa^2 vanishes on the
       plane N' of the 3-dim space C x W_P: rank G <= 2.  But G is block diagonal with e_3 = m_a m_b m_c != 0, beta != 0 and, in the
       coordinates (lam_a, lam_b), Q_m = -m_b lam_a^2 - m_a lam_b^2 - 2(m_a+m_b) lam_a lam_b of determinant -(m_a^2 + m_a m_b + m_b^2) = -<m,m>/2.
       So rank G = 3 unless <m,m> = 0.  QED
   Remarks. (i) For ISOTROPIC m = (1,w,w^2,0,0) the proof shows instead: Q_m = -(lam_b - w^2 lam_a)^2, Z_* = chi_1 mbar^T with mbar = (1,w^2,w)
   = 1/m, and N is one of the four explicit planes {lam_b - w^2 lam_a = xi kappa}, xi^2 = -3/(32 beta), beta = +-sqrt(3)/4.  These ARE 2-dim
   level spaces with defect line C m (r4_pr3.py (2): 1e-13) - non-split, not containing any single-row matrix.  [NUMERICAL] they are maximal:
   no one-vector extension with defect in C m in 60 calibrated starts, so there is numerically no principal (5,1) for this m either.
   (ii) The N-problem for larger support [NUMERICAL, r4_n2.py, LM on Gr(2, 3|P|-2), calibrated by |P| = 3: good m 0 injective solutions
   among 169 hits, isotropic m 50 among 243]: |P| = 4: (1,2,3,-6,0): 0 injective among 19 hits; isotropic (1,i,-1,-i,0): 0/20;
   (1,2,-4,1,0) (a REPEATED entry): 8 injective among 38, none of which extends to dimension 3 (0/64 starts; caveat: these N are LM
   output with residual 1e-10..1e-9, so the extension test had to be run with acceptance tolerance 1e-7 - less sharp than the other tests); |P| = 5: (1,2,3,-1,-5): 0/11,
   isotropic fifth roots: 0/15.  So the N-problem seems to have no solution for m with distinct nonzero entries outside the isotropic
   3-support case - a small polynomial system (two matrices on |P| columns), i.e. a finite exact computation for |P| = 4, 5.

 R4.6 THE SUGGESTED TRICKS, AND WHY THEY DO NOT CLOSE THE CASE (rigorous remarks).
   (a) m in two slots / isotropic split case.  If e_i m^T in L' and <m,m> = 0, pairing C(Y) = D_i(Y) l_i with m gives 0 = mu(Y) <m, y^i>,
       and mu(0) = -6, so <m, y^i> = 0 on L' (row i of L' lies in m^perp); Per(.., m, .., m) = <m, D_i m> = 0.  But both are already
       consequences of the LINEAR part of D_i(Y) m = mu m (which gives <c',m> = 0 and c'_j constant on P for the column sums c' of the other
       three rows; then y^i = kappa m - c').  So the two-slot pairing carries no new information when m is isotropic; the non-isotropic
       proof works only because <m,m> != 0 lets one solve for thetahat.  [r4_i2.py confirms both on the isotropic split examples.]
   (b) Lemma EQ over all pairs = "merged columns".  For m_a != m_b, m_b C_a - m_a C_b = 24(m_b - m_a) says that the 4 x 4 space
       { [ (m_b y_b - m_a y_a)/(m_b - m_a), y_k, y_l, y_n ] } is level.  The vectors m_b e_a - m_a e_b span m^perp, so all these identities
       together are exactly <w, C(Y)> = 24 sum w for w in m^perp - the definition of the defect line.  No new information; what Lemma EQ adds
       is the bound 3 for the FIXED subspaces {y_a = y_b}; in a 5-dim space this only says rank(Y -> y_a - y_b) >= 2 for each pair with m_a != m_b.
   (c) Rows' R3.10 target "dim Pi_0 <= 2".  In the split case let Pi be the projection of L' to the three rows != i (dim Pi = dim L' - 1,
       the kernel is C e_i m^T) and c' the column sums of those rows.  The linear part of D_i(Y) m = mu m gives c' in span(1, e_n : n neutral)
       on Pi (c'_j is constant on P).  With Pi_0 := {c' in C 1} (rows' definition in the 3-support case) a (5,1) has dim Pi_0 >= 4 - (5 - |P|)
       = |P| - 1.  So a bound dim Pi_0 <= 2 excludes the isotropic split (5,1) for |supp m| >= 4 but NOT for the isotropic 3-support line
       (1,w,w^2,0,0), where dim Pi_0 = 2 is allowed and one needs in addition that the two forms c'_n, c'_n' cannot be independent on Pi.

 R4.7 NUMERICS OF THIS ROUND (all flagged numerical).
   r4_z4.py, r4_z4c.py, Gr(4,15), column-centred 4-dim spaces with defect in C m [(SL_m)]: two-column control 3/49 converged (all genuinely
   defect 1) in one run and 0/33 in a second run; isotropic (1,w,w^2,0,0) 0/36; isotropic (1,i,-1,-i,0) 0/36; isotropic fifth roots 0/60;
   (1,2,3,-1,-5) 0/60; (1,2,-3,0,0) 0/35.  THE CONTROL RATE IS ONLY ABOUT 4% (3/82), so each of these negatives is WEAK evidence
   (an equally frequent family would be missed with probability 0.1 - 0.3 per line); do not rely on them.
   r4_climb2.py, isotropic m = (1,w,w^2,0,0): 18 greedy climbs from the line C chi_1 mbar^T (extensions are found at 2-5 of 6 starts per
   step, so the search is live): all stop at dimension 2 or 3 (ker kappa of dim <= 3 and rank s <= 1); none reaches dimension 4.
   The better-calibrated negative evidence remains the extension searches (R3.7: 0/56 with control 8/8; here 0/60 and 0/64).
   r4_pr3.py, r4_n2.py, r4_climb.py: see R4.5.  r4_test1.py: R4.3 check and the cubic identity for column-centred spaces
   (E_3 := sum_{a<b<c} tau(y_a y_b y_c) = 0 and tau((b_j+s)(2b_j^2 + 3s^2 - sum_k b_k^2)) = -16 theta_3 m_j, checked to 1e-10 on the four
   genuine column-centred (3,1) spaces).

 R4.8 WHAT IS LEFT OF (DI_5) AT e = 1, AND e = 2, 3.
   NOT PROVED: (DI_5) at e = 1.  Proved so far: two-column m (TC5); split non-isotropic (SPLIT); principal with |supp m| = 3 non-isotropic (PR3).
   Open, in decreasing order of evidence that they are empty:
   (o1) principal (5,1) spaces for |supp m| >= 4 or m isotropic: by PS these are H (+) N with N a solution of the N-problem; numerically
        the N-problem has no solution for distinct entries and |P| >= 4, and the solutions that exist do not extend.  Exact statement to prove:
        "the N-problem has no solution" (|P| = 4, 5, distinct entries) and "N (+) C eta is never level with defect in C m" otherwise.
   (o2) non-principal (5,1) spaces: ker kappa (4-dim, column-centred, defect line C m) contains no principal H.  By QB, for q = rank s|_ker kappa = 3
        and a neutral column, ker kappa = H' (+) C Z_* with Z_* doubly centred and supported on P, but H' is not strongly level and the columns
        of Z_* need not be isotropic (<z^*_j,z^*_j> = x m_j).  For q <= 2 the doubly centred part has dim >= 2.  No such 4-dim space is known
        for non-two-column m; this is (SL_m) and needs the cubic/quartic analysis of blueprint S3-S8 with the extra form (not done).
   e = 2, 3: the method of PS gives only the normal form.  If ker(c) contains a principal H then L' = H (+) N, N = ker s, and
        z_j = (c_j(Z)/4) 1 - B_j (phi_Z)_j with phi_Z in V (x) C(L') (i.e. sum_j w_j (phi_Z)_j = 0 for w in C(L')^perp), and the vector
        (4 <(phi_Z)_j,(phi_Z)_j> - 3 c_j(Z)^2)_j lies in C(L').  For e = 1 this forces dim N <= 2; for e >= 2 it gives no bound of the
        required strength (Z -> phi_Z maps N to V (x) C(L'), of dim 3e, with kernel inside {1 c^T/4 : c in C(L')}), so (6,2) and (7,3) are
        NOT reached; rigorous there remain FS (one-row split, nondegenerate C) and TS only.

## DI5-R5 (round 5): towards (SL_m) = "Lemma SL with the extra form"; the stratum |supp m| = 3

 Setting for the whole section.  m != 0, sum m = 0, P = supp m; K is a COLUMN-CENTRED linear space of 4 x 5 matrices with
 C(Y) = 24*1 + thetahat(Y) m on K;  thetahat = theta_2 + theta_3 + theta_4 (homogeneous parts; polynomials on K because m != 0).
 Blueprint notation: s(Y) row-sum vector, S = s(K), q = dim S, N = K cap ker s (the doubly centred part), d = dim N, dim K = q + d,
 q_j(Y) = <y_j,y_j> - <s,y_j>, T_j(Y) = sum over triples not containing j of tau(y_a y_b y_c), b_j(Y) = 2y_j - s(Y).
 A column n with m_n = 0 is NEUTRAL.  (SL_m): dim K <= 3.

 R5.1 LEMMA C' (column form with defect; replaces Lemma C; rigorous).  K as above satisfies, for all Y, Y' in K and j in [5]:
   (C1)   all columns lie in V;
   (C2')  q_j(Y) = vartheta(Y) m_j,  vartheta := -theta_2/2 (ONE quadratic form on K);  and sum_a <y_a,y_a> = <s,s>;
          polarised:  2<y_j,y'_j> - <s(Y),y'_j> - <s(Y'),y_j> = 2 m_j Theta(Y,Y')  (Theta = polar form of vartheta);
          equivalently  <b_j(Y),b_j(Y')> = <s(Y),s(Y')> + 4 m_j Theta(Y,Y'),  i.e.  b_j^* g = s^* g + 4 m_j vartheta   (the PENCIL);
   (C3')  2 T_j(Y) = theta_3(Y) m_j;      (C4')  [y_a,y_b,y_c,y_d] = theta_4(Y) m_j,  {a,b,c,d} = [5] \ {j}.
   Proof: (ID2) of the blueprint, degree by degree; for degree 2: sum_{a<b != j} <y_a,y_b> = (<s,s> - Q)/2 + q_j (Q = sum <y_a,y_a>),
   so -(<s,s> - Q) - 2 q_j = theta_2 m_j; summing over j gives Q = <s,s>.  (This is Lemma QB at kappa = 0.)  QED
   WHAT SURVIVES OF THE BLUEPRINT (any m):
   * for a NEUTRAL column n everything in S3-S5 that concerns column n alone survives verbatim, because q_n == 0:
       (Nn)   on N the n-th column lies in an isotropic line C v_n or is 0  (Lemma N);
       (B1n)  <b_n(Y),b_n(Y')> = <s(Y),s(Y')>;   (B3n)  <z_n, b_n(Y)> = 0 for Z in N, Y in K;
       (B-i') q = 3  =>  z_n = 0 for all Z in N   [b_n^*g = s^*g has rank 3, so b_n(K) = V];
       (B-ii') q = 2 and S nondegenerate  =>  z_n = 0 for all Z in N   [b_n(K) is a nondegenerate plane].
   * for columns in P: Lemma N is replaced by <z_j,z_j> = vartheta(Z) m_j on N (the columns of P are isotropic exactly on the quadric
     {vartheta = 0} of N), Lemma B by the pencil; (B-i) FAILS (q = 3 no longer forces N = 0), Lemma A and S6-S8 have to be redone.
   * the conditions for deleting a neutral column are exactly those of the strongly level case (T_n = 0, bracket = 0).

 From here on |P| = 3: P = {a,b,c}, neutral columns n, n'.  W_P := zero-sum vectors supported on P.  For l in W_P:
 Q_m(l) := m_a l_b l_c + m_b l_a l_c + m_c l_a l_b.   N_P := {Z in N : z_n = z_n' = 0}.   nu(Y) := (y_n, y_n'), w(Y) := y_n + y_n'.

 R5.2 LEMMA 3C (rigorous; ANY m with |supp m| = 3).  If y_n = y_n' = 0 for all Y in K ("K is a 3-column space") then dim K <= 3.
   Proof. (1) For a 3-column Y, (C2') reads -<y_a,y_b> - <y_a,y_c> = vartheta m_a and cyclically, whence
        <y_b,y_c> = vartheta m_a,  <y_a,y_c> = vartheta m_b,  <y_a,y_b> = vartheta m_c;        and (C3'_n) reads  tau(y_a y_b y_c) = 0.
   (2) Diagonalisation.  Write y_a = m_c Y'_b + m_b Y'_c, y_b = m_c Y'_a + m_a Y'_c, y_c = m_b Y'_a + m_a Y'_b (invertible: det = 2 m_a m_b m_c).
       For u in C^3 with <u,m> = 0:  u_a<y_b,y_c> + u_b<y_a,y_c> + u_c<y_a,y_b> = e_3(m) sum_j (u_j/m_j) <Y'_j,Y'_j>   [ID10, r5_checks.py (v3)].
       By (1) the left side is vartheta <u,m> = 0, so (<Y'_j,Y'_j>/m_j)_j is orthogonal to m^perp:
           <Y'_j,Y'_j> = vartheta''(Y) m_j^2  (j in P)  for ONE quadratic form vartheta'' on K.
   (3) Let rho_j : K -> V, Y -> Y'_j; rho_j^* g = m_j^2 vartheta''; the three rho_j are jointly injective.  Let r = rank vartheta'',
       R = its radical.  ker rho_j is in R, and rho_j(R) is totally isotropic and orthogonal to rho_j(K).
       r >= 2: rho_j(K) is nondegenerate (a plane, or V), so rho_j(R) = 0 for all j, R = 0, dim K = r <= 3.
       r = 0: K = R embeds into the sum of three isotropic lines: dim K <= 3.
       r = 1: dim K = 1 + dim R <= 4, and dim K = 4 forces R = {Y' = (t_a v_a, t_b v_b, t_c v_c)} with isotropic v_j != 0.
   (4) Exclusion of r = 1, dim K = 4.  On R, y_a = m_c t_b v_b + m_b t_c v_c etc., and tau(y_a y_b y_c) == 0 in t gives (coefficients of
       t_j^2 t_k and of t_a t_b t_c):  tau(v_j^2 v_k) = 0 for all j != k, tau(v_a v_b v_c) = 0.  For proportional v_j, v_k this is
       tau(v_j^3) = 0 (chi-type, (P-b)); for non-proportional ones the pair is one of the 7 pairs of S7 (II-a): the four zeta-pairs
       {zeta_k, conj zeta_k} (common zero in row k; there tau(v^3) != 0) or the three conjugate chi-pairs (a = 0, b^2 = -4 in (ID7),
       and {chi_1, chi_3}).  These 7 pairs are disjoint, so three lines pairwise compatible are {chi,chi,chi} or {chi,chi,conj chi};
       after a row permutation v_j in {chi_1, chi_3}, and v_j^perp cap V = span(v_j, chi_2).
       Take Y_0 in K \ R: eta_j := rho_j(Y_0) is orthogonal to v_j (polarisation, vartheta'' has radical R) with <eta_j,eta_j> =
       m_j^2 vartheta''(Y_0) != 0; so eta_j = x_j v_j + (eps_j m_j mu_0) chi_2, eps_j = +-1; subtract an element of R and rescale:
           K = { Y' = (t_a v_a + eps_a m_a mu chi_2,  t_b v_b + eps_b m_b mu chi_2,  t_c v_c + eps_c m_c mu chi_2) }.
       Then y_a = m_c t_b v_b + m_b t_c v_c + mu m_b m_c (eps_b + eps_c) chi_2, and the mu t_a^2 coefficient of tau(y_a y_b y_c) is
       m_b^2 m_c^2 (eps_b + eps_c) tau(chi_2 v_a^2) = 4 m_b^2 m_c^2 (eps_b + eps_c)  (tau(chi_2 chi_1^2) = tau(chi_2 chi_3^2) = 4).
       So eps_b + eps_c = 0, likewise eps_a + eps_c = 0 and eps_a + eps_b = 0: impossible for signs.  QED
   [Sanity, r5_3col.py: 3-dim 3-column spaces are found at 66/76 and 58/67 LM starts (half of them with genuine defect), 4-dim ones at
    0/58 and 0/42, for m = (1,2,-3,0,0) and (1,w,w^2,0,0).]

 R5.3 LEMMA NP (the doubly centred part supported on P; rigorous).
   For Z in N_P:  <z_j,z_j> = vartheta m_j, <z_a,z_b> = vartheta m_c (cyclically), tau(z_a z_b z_c) = 0, theta_3(Z) = theta_4(Z) = 0.
   (a) m NON-ISOTROPIC:  dim N_P <= 2.  If dim N_P = 2 then, after a row permutation, N_P is
         TYPE I':  chi_1 (x) W_P                         (vartheta = 0 on it; this is the type I plane of the blueprint), or
         TYPE V:   chi_1 (x) c^+ (+) chi_3 (x) c^-       (vartheta != 0),  c^+, c^- the two roots of Q_m in P(W_P); c^+_j c^-_j = k_0 m_j.
       Every type V plane IS a doubly centred (2,1) space with defect line C m (new exact family; r5_checks.py: 1e-12 for three m).
   (b) m ISOTROPIC, m = (1,w,w^2) on P, mbar := (1,w^2,w):  dim N_P <= 3, and {Z in N_P : z_a = w z_b} = U (x) mbar with U a subspace
       of one of the three planes {x in V : x_0 + x_k = 0}, k = 1,2,3.  U_2 (x) mbar, U_2 = {(x,y,-x,-y)}, IS a doubly centred (2,1)
       space with defect line C m (thetahat = -2<u,u>; r5_checks.py).
   Proof. <z_c,z_c> = <z_a+z_b,z_a+z_b> gives the cross terms; (C3'_n) is tau(z_a z_b z_c) = 0, and (C3'_a), (C4') contain no
   nonzero term, so theta_3 = theta_4 = 0 on N_P.  For (al,be) in C^2:  <al z_a + be z_b, al z_a + be z_b> = vartheta Phi(al,be),
   Phi := m_a al^2 + 2 m_c al be + m_b be^2, of discriminant 4(m_c^2 - m_a m_b) = 2<m,m>.
   (a) Phi has two distinct roots (al_+-, be_+-); iota_+-(Z) := al_+- z_a + be_+- z_b have totally isotropic images, i.e. lines C v_+-
   or 0 (Q1), and (iota_+, iota_-) is injective on N_P.  So dim N_P <= 2, and dim N_P = 2 means N_P = v_+ (x) c^+ (+) v_- (x) c^- with
   non-proportional c^+-. in W_P.  If v_+ is proportional to v_-: N_P = v (x) W_P and tau(z_a z_b z_c) = e_3(l) tau(v^3) forces tau(v^3) = 0,
   v = chi_1 (P-b): type I'.  Otherwise <v_+,v_-> != 0 (Q2) and <z_j,z_j> = 2 lam_+ lam_- c^+_j c^-_j <v_+,v_-> = vartheta m_j gives
   c^+_j c^-_j = k_0 m_j with k_0 != 0 (two zero-sum vectors on three points have a common nonzero coordinate); so all c^+-_j != 0 and,
   as sum c^- = 0, Q_m(c^+) = e_3(c^+) sum m_j/c^+_j = 0.  The cubic: lam_+^3: e_3(c^+) tau(v_+^3) = 0;  lam_+^2 lam_-:
   tau(v_+^2 v_-) e_3(c^+) k_0 D_+ = 0 with D_+ := sum_j m_j/(c^+_j)^2; with x_j := 1/c^+_j we have <m,x> = 0 = <m,1>, so m is a multiple
   of (x_b - x_c, x_c - x_a, x_a - x_b) and D_+ is a nonzero multiple of the Vandermonde of x, which is != 0 because all m_j != 0.
   So tau(v_+^3) = tau(v_-^3) = tau(v_+^2 v_-) = tau(v_+ v_-^2) = 0: a conjugate chi-pair, WLOG (chi_1, chi_3): type V.  Conversely all
   coefficients vanish for (chi_1, chi_3) (tau(chi_1^3) = tau(chi_1^2 chi_3) = tau(chi_1 chi_3^2) = tau(chi_3^3) = 0).
   (b) Phi = w (be + w al)^2: only iota(Z) = z_a - w z_b is isotropic-valued, its image is a line or 0, and its kernel consists of
   Z = x (x) mbar (z_a = w z_b, z_c = w^2 z_b); the cubic is e_3(mbar) tau(x^3) = tau(x^3) = 3 (x_0+x_1)(x_0+x_2)(x_0+x_3) on V, so a
   linear space of such x lies in one of the three planes.  QED

 R5.4 LEMMA T (top-degree constraints; rigorous; any m with |P| = 3).  Let Z = chi_1 l^T in K, l in W_P.  Then for every Y in K:
   (al)  l_a l_b l_c <chi_3, y_n> = 0  and  l_a l_b l_c <chi_3, y_n'> = 0;
   (be)  ( l_b l_c, l_a l_c, l_a l_b ) <chi_2, w(Y)>  is a multiple of (m_a, m_b, m_c);
   (de)  ( l_b l_c, l_a l_c, l_a l_b ) beta(Y)  is a multiple of (m_a, m_b, m_c),  beta(Y) := [chi_1,chi_1,y_n,y_n'];
   (ep)  sum_{pairs {p,p'} of P} l_p l_p' <chi_2, y_p''> + e_2(l) <chi_2, y_n'> = 0,  and the same with y_n in place of y_n'.
   Hence, if all l_j != 0 and l is not proportional to 1/m := (1/m_a, 1/m_b, 1/m_c):
       y_n = k chi_2 + rho_n chi_3,   y_n' = -k chi_2 + rho_n' chi_3,   rho_n rho_n' == 0 on K   (so rho_n == 0 or rho_n' == 0 on K).
   Proof. Y + t Z is in K for all t.  (al): t^3-coefficient of (C4'_n'): l_a l_b l_c [chi_1,chi_1,chi_1,y_n] = -6 l_a l_b l_c <chi_3,y_n>,
   and the right side theta_4 m_n' is 0.  (be): t^2-coefficient of (C3'_a): the triples of {b,c,n,n'} containing b and c give
   l_b l_c tau(chi_1^2 (y_n + y_n')) = l_b l_c <chi_2,w>, equal to m_a times the t^2-coefficient of theta_3(Y+tZ)/2; same for b, c.
   (de): t^2-coefficient of (C4'_a): l_b l_c [chi_1,chi_1,y_n,y_n'].  (ep): t^2-coefficient of (C3'_n) and (C3'_n').
   [All four coefficient formulas checked at random points to 2e-14, r5_lemT.py.]
   If l_a l_b l_c != 0 and l is not proportional to 1/m, the vector (l_b l_c, l_a l_c, l_a l_b) = e_3(l)/l is not proportional to m, so
   <chi_2,w> = 0 and beta(Y) = 0; with (al): y_n, y_n' in span(chi_2, chi_3), and beta = 8 rho_n rho_n' there (ID8-type identity:
   [chi_1,chi_1,u,u'] = -6<chi_2,uu'> + 2<chi_1,u><chi_1,u'>).  rho_n, rho_n' are linear forms on K.  QED
   The same holds with chi_1 and chi_3 exchanged (row permutation k -> -k, which fixes chi_2).

 R5.5 PROPOSITIONS I' AND V (rigorous).
   PROP I' (ANY m with |P| = 3).  If K contains chi_1 (x) W_P then dim K <= 3; more precisely K lies in chi_1 (x) C^P (3-column, "R3")
   or in chi_1 (x) W_P (+) C chi_3 (e_n - e_n')^T.
   Proof. Lemma T for all l in W_P.  (al) with l_a l_b l_c != 0: <chi_3,y_n> = <chi_3,y_n'> = 0.  (be) with l = (1,-1,0): l_b l_c = 0, so
   the multiple of m is 0 and l_a l_b <chi_2,w> = 0: <chi_2,w> = 0.  (ep) with l = (1,-1,0): <chi_2,y_c> = -<chi_2,y_n'> = -<chi_2,y_n>;
   with <chi_2,w> = 0: <chi_2,y_n> = <chi_2,y_n'> = <chi_2,y_c> = 0, and likewise for a, b.  So on K: y_n = al_n chi_3, y_n' = al_n' chi_3,
   y_j = p_j chi_1 + r_j chi_3 (j in P), s = s_1 chi_1 + s_3 chi_3.
   (C2'pol) between Y and Z = chi_1 x^T (x in W_P), column j in P:  x_j <2y_j - s, chi_1> = 2 m_j Theta(Y,Z); the right side is linear in x,
   Theta(Y, chi_1 x^T) = sum_k th_k x_k; x = e_k - e_k' with k, k' != j gives th_k = th_k' for all pairs, so Theta(Y,Z) = th sum x = 0 and
   <2y_j - s, chi_1> = 0: r_j = s_3/2 (j in P).  Comparing chi_3-coefficients in sum_j y_j = s: s_3 = -2(al_n + al_n').
   (C4'_n') and (ID8) with p = (p_a,p_b,p_c,0), r = (s_3/2,s_3/2,s_3/2,al_n):  0 = [y_a,y_b,y_c,y_n] = al_n s_3 (4 e_2(p_a,p_b,p_c) - 3 s_3^2);
   replacing Y by Y + chi_1 x^T changes only p -> p + x, and e_2(x) is not == 0 on W_P: al_n s_3 = 0, likewise al_n' s_3 = 0, so
   s_3^2 = -2(al_n + al_n') s_3 = 0: s_3 == 0, al_n' = -al_n, r_j = 0.  (C2'_n): 0 = <y_n,y_n> - <s,y_n> = -4 al_n s_1, so al_n == 0 or s_1 == 0
   on K (linear forms).  al_n == 0: K in chi_1 (x) C^P.  s_1 == 0: s == 0 and K in chi_1 (x) W_P (+) C chi_3 (e_n - e_n')^T.  QED
   PROP V (m non-isotropic).  If N_P is a type V plane then K is a 3-column space, hence dim K <= 3 (Lemma 3C).
   Proof. c^+ has no zero entry and is not proportional to 1/m (sum_j 1/m_j = -<m,m>/(2 e_3(m)) != 0), and e_2(c^+) != 0 (a zero-sum l with
   e_2(l) = 0 is a multiple of (1,w,w^2) or (1,w^2,w), and Q_m(1,w,w^2) = m_a + w^2 m_b + w m_c vanishes only for m proportional to
   (1,w^2,w), which is isotropic).  Lemma T for chi_1 c^+T: y_n = k chi_2 + rho_n chi_3, y_n' = -k chi_2 + rho_n' chi_3.  Lemma T with
   chi_1, chi_3 exchanged, for chi_3 c^-T: the chi_3-coefficients vanish, rho_n = rho_n' = 0.  (ep) for chi_1 c^+T, difference of its two
   versions: e_2(c^+) <chi_2, y_n' - y_n> = -8 k e_2(c^+) = 0, so k = 0.  QED

 R5.6 THEOREM SL3-RED (rigorous): what is left of (SL_m) for |supp m| = 3, m NON-ISOTROPIC.
   Let dim K = 4.  Then dim N_P <= 1, and K is of one of the following four kinds (types (q,d)):
     (R1)  (3,1):  N = C Z_* inside N_P with vartheta(Z_*) != 0   [Z_* = v_+ c^+T + v_- c^-T, <v_+,v_-> != 0, c^+_j c^-_j = k_0 m_j,
                   one cubic relation tau(z_a z_b z_c) = 0 between the isotropic v_+, v_-];
     (R2)  (3,1):  two entries of m are equal, m_a = m_b (so m is a multiple of (1,1,-2,0,0)), and N = C v (e_a - e_b)^T, v isotropic;
     (R3)  (2,2):  S = u^perp for an isotropic u, and at least one neutral column is active on N;
     (R4)  (1,3):  both neutral columns are active on N and dim N_P = 1.
   In particular: type (0,4) is impossible, and for m with three DISTINCT nonzero entries a 4-dim K of type (3,1) must have
   vartheta(Z_*) != 0.
   Proof. dim N_P <= 2 (NP), and dim N_P = 2 gives dim K <= 3 by Prop I' or Prop V.  So dim N_P <= 1.
   Type (0,4): K = N; by (Nn) nu maps N into C v_n x C v_n', so dim N_P >= 2.  Contradiction.
   Type (1,3): dim N_P >= 1, hence = 1, and nu(N) is 2-dim: (R4).
   Type (2,2): N is not inside N_P, so some neutral column is active on N, and (B-ii') forces S degenerate: S = u^perp: (R3).
   Type (3,1): N = C Z_* and Z_* is in N_P by (B-i').  Suppose vartheta(Z_*) = 0.  Then the three columns of Z_* are isotropic, pairwise
   orthogonal, so Z_* = v l^T with v isotropic and l in W_P \ 0 (Q1).
    (i) all l_j != 0: tau(z_a z_b z_c) = e_3(l) tau(v^3) = 0, so v = chi_1 after a row permutation; l is not proportional to 1/m (sum l = 0,
        sum 1/m_j != 0).  Lemma T: y_n = k chi_2 + rho_n chi_3, y_n' = -k chi_2 + rho_n' chi_3 and, say, rho_n == 0 (the other case is
        symmetric).  (C2'_n): 4k^2 = k <s,chi_2>, so k == 0 or 4k == <s,chi_2>.
        k == 0: y_n == 0, y_n' = rho_n' chi_3, and (C2'_n'): rho_n' <s,chi_3> == 0; as q = 3, <s,chi_3> is not == 0, so rho_n' == 0 and K is
        a 4-dim 3-column space, contradicting Lemma 3C.
        4k == <s,chi_2>: (C2'_n') reads 4k^2 = -4k^2 + rho_n' <s,chi_3>, i.e. rho_n' <s,chi_3> = <s,chi_2>^2/2; as q = 3 the linear forms
        <s,chi_2>, <s,chi_3> on K are independent, so <s,chi_3> does not divide <s,chi_2>^2.  Contradiction.
    (ii) some l_j = 0, say Z_* = v (e_a - e_b)^T.  (C2'pol) between Y in K and Z_*: column c gives 0 = 2 m_c Theta(Y,Z_*), so Theta(.,Z_*) = 0,
        and columns a, b give <b_a(Y),v> = <b_b(Y),v> = 0.  So b_a(K), b_b(K) lie in v^perp cap V, on which g has rank 1: the forms
        s^*g + 4 m_a vartheta and s^*g + 4 m_b vartheta have rank <= 1 on K.  If m_a != m_b then s^*g, a combination of the two, has
        rank <= 2, but q = 3.  So m_a = m_b: (R2).     QED
   REMARKS.  (1) The two-column counterexamples to (SL_m) live in type (2,2) with S degenerate [r5_climb_r2.py: for m = (1,-1,0,0,0) a
   greedy climb from zeta (e_0 - e_1)^T reaches a column-centred (4,1) space of type (2,2)], i.e. in the analogue of (R3); so (R3) is
   where "m is not two-column" has to be used, and it is the analogue of blueprint S7/S8.  (2) For (R1) the constraints already
   available are, for all Y in K (u = y_n, u' = y_n', w = u + u'; proofs as for Lemma T):
       <om,u> = <om,u'> = 0 with om := -6 z_a z_b z_c + vartheta(Z_*) sum_P m_j z_j;   (<z_b z_c,w>, <z_a z_c,w>, <z_a z_b,w>) in C m;
       ([z_b,z_c,u,u'], [z_a,z_c,u,u'], [z_a,z_b,u,u']) in C m;   and B_n, B_n' are isometries of V with u = (B_n + 1)sigma/2.
   If these force u = u' = 0, Lemma 3C finishes (R1); I could not decide this by hand in the time (one-parameter family of Z_*).
   (3) [NUMERICAL] for m = (1,1,-2,0,0) greedy climbs from v (e_0 - e_1)^T (v = zeta, chi_1, generic) stop at dim <= 3 (r5_climb_r2.out).

 R5.7 THE OTHER STRATA (status; nothing proved beyond R5.1 and the items listed).
   |supp m| = 3, m isotropic (m = (1,w,w^2) on P): Lemma 3C, Lemma T and Prop I' hold (they do not use isotropy); NP gives only
     dim N_P <= 3, and the exceptional direction of Lemma T is exactly l = mbar = 1/m (this is where the planes N of R4.5 (i) and
     U_2 (x) mbar live).  Type (0,4) is not excluded by the argument of R5.6 (it needs dim N_P <= 1 or the Props).  Open.
   |supp m| = 4 (one neutral column n): R5.1 gives (Nn), (B-i'), (B-ii') for that column only; N is supported on P when q = 3, but four
     P-columns with <z_j,z_j> = vartheta m_j and sum z_j = 0 no longer determine the cross terms <z_j,z_k>, so NP has no analogue yet.
     Pencil: if m has four distinct nonzero entries and q = 3, d = 1 then vartheta(Z_*) = 0 (det(s^*g + x vartheta) has the five roots
     0, 4m_j; R4.3-type argument), the columns of Z_* are isotropic and Theta(.,Z_*) = <phi,s(.)> with phi isotropic, phi != 0 (if phi = 0 then b_j(K) lies in (z^*_j)^perp for every active column j, so s^*g + 4 m_j vartheta has rank <= 1 for two different values of m_j and s^*g would have rank <= 2).  Open.
   |supp m| = 5 (no neutral column): only the pencil; nothing of S3-S8 survives directly.  Open.

 R5.8 NUMERICS OF ROUND 5 (flagged numerical) AND REQUESTS TO THE COMPUTE MACHINE.
   r5_types.py (Gr(3,15), m = (1,2,-3,0,0), 19 hits/65 starts): 18 of type (3,0) (11 with genuine defect, neutral columns of every rank
   pattern from [0,0] to [2,3]), 1 strongly level of type (1,2).  So 3-dim column-centred spaces with defect are plentiful and of type
   (3,0); none with d >= 1 and defect was seen.   r5_checks.py, r5_lemT.py, r5_3col.py: checks quoted above.
   /home/claude/work/L-gct-210/COMPUTE-verifyfl.md: requests A (the four isotropic planes N have no extension; exact, small),
   B (N-problem for |P| = 4, 5; exact), C (calibrated Gr(4,15) searches), D (direct (5,1) searches), E (extension varieties of explicit
   2-dim spaces for m = (1,2,-3,0,0)), F (typed searches for the residual kinds (R1)-(R4)).

 R5.9 THE BLUEPRINT'S EXTREMAL PLANES (types I and II) NEVER SIT IN A 4-DIM K WHEN |supp m| = 3 (rigorous; added 20:00).
   These are the configurations of blueprint S7/S8; for two-column m the type II plane DOES extend to a 4-dim column-centred space
   (numerically 3 of 3 climbs, r5_climb_r3.py), for |supp m| = 3 it does not (0 of 6 climbs; proved below).
   PROP I-ALL (any m with |supp m| = 3).  Let M be a 3-set of columns, Lam_M the zero-sum vectors supported on M.  If K contains
   chi_1 (x) Lam_M then dim K <= 3 (for M != P: K lies in chi_1 (x) C^M).
   Proof. M = P is Prop I'.  Let M != P, {o,o'} the complement; then M contains a column of P and so does {o,o'}.  For Y in K and
   x in Lam_M, Y + t chi_1 x^T is in K; the four coefficient identities of Lemma T hold with (P; n, n') replaced by (M; o, o') (they are
   identities in the columns), now with right sides theta m:
    t^3 of (C4'): deleting i in M cap P there is no t^3-term, so the t^3-coefficient of theta_4 vanishes, and deleting o', o gives
       x_i x_j x_k <chi_3,y_o> = 0 = x_i x_j x_k <chi_3,y_o'>:   <chi_3,y_o> = <chi_3,y_o'> = 0.
    t^2 of (C3'_i), i in M:  x_j x_k <chi_2, y_o + y_o'> = rho m_i.  With j in M cap P and x = e_j - e_k (x_i = 0): deleting j gives rho = 0,
       deleting i gives <chi_2, y_o + y_o'> = 0.  Then rho = 0 for every x (delete j in M cap P).
    t^2 of (C3'_o), (C3'_o') with x = e_j - e_k:  <chi_2,y_i> + <chi_2,y_o'> = 0 = <chi_2,y_i> + <chi_2,y_o>;  so <chi_2,y_o> = <chi_2,y_o'> = 0
       and <chi_2,y_i> = 0 for every i in M.
   Hence y_o = al_o chi_3, y_o' = al_o' chi_3, y_i = p_i chi_1 + r_i chi_3 (i in M), s = s_1 chi_1 + s_3 chi_3.  (C2'pol) between Y and
   Z = chi_1 x^T: a column of P outside M gives Theta(Y,Z) = 0, then column i in M gives <2y_i - s,chi_1> = 0, r_i = s_3/2, and
   s_3 = -2(al_o + al_o').  By (ID8):  [y_i,y_j,y_k,y_o] = al_o s_3 (4 e_2(p) - 3 s_3^2) = theta_4 m_o',  the same with o, o' exchanged, and
   [y_j,y_k,y_o,y_o'] = al_o al_o' (8 p_j p_k - 6 s_3^2) = theta_4 m_i (i in M)   [both checked numerically].  Replace Y by Y + chi_1 x^T
   (p -> p + x) and compare the parts quadratic in x, tau_2 := that part of theta_4:
       4 al_o s_3 e_2(x) = tau_2 m_o',   4 al_o' s_3 e_2(x) = tau_2 m_o,   8 al_o al_o' x_j x_k = tau_2 m_i  (i in M).
   M contains a neutral column i_0 (as M != P): al_o al_o' = 0; then a column i in M cap P gives tau_2 = 0, so al_o s_3 = al_o' s_3 = 0,
   s_3^2 = -2(al_o + al_o') s_3 = 0, s_3 = 0, al_o' = -al_o, al_o^2 = 0.  So y_o = y_o' = 0, r_i = 0: K lies in chi_1 (x) C^M.  QED
   PROP II-ALL (|supp m| = 3, m non-isotropic).  If K contains a plane N_0 = { mu v (e_i - e_j)^T + mu' v' (e_k - e_l)^T } with v, v'
   non-proportional isotropic and i, j, k, l distinct, then dim K <= 3.
   Proof. Step 0: N_0 is the strongly level type II plane.  Let o be the fifth column.  On N_0 (ID4): T_i = mu mu'^2 tau(v v'^2) = -T_j,
   T_k = mu^2 mu' tau(v^2 v') = -T_l, T_o = 0, and the only nonzero bracket is [Z^(o)] = mu^2 mu'^2 [v,v,v',v'].  (C3'): theta_3 (m_i + m_j) = 0
   = theta_3 (m_k + m_l); both sums cannot vanish when |supp m| = 3, so theta_3 = 0 on N_0 and tau(v v'^2) = tau(v^2 v') = 0.  (C4') for a
   column of P among i,j,k,l: theta_4 = 0, so [v,v,v',v'] = 0.  By (II-a), v = zeta, v' = conj(zeta) after a row permutation and rescaling.
   [For two-column m = e_i - e_j one has m_i + m_j = 0 and theta_3 need not vanish: this is exactly the escape of the two-column case.]
   Step 1 (ID11, checked to 2e-14, r5_propII.py): for column-centred Y, Z = mu zeta (e_i - e_j)^T + mu' zb (e_k - e_l)^T (zb := conj zeta,
   1_3 := (1,1,1,0) = zeta zb), the t^2-coefficients of T_c(Y + tZ) are
       c = o:  -mu^2 <zb, y_k + y_l> - mu'^2 <zeta, y_i + y_j>;
       c = i:   mu mu' <1_3, y_k - y_l> - mu'^2 <zeta, y_j + y_o>;        c = j:  -mu mu' <1_3, y_k - y_l> - mu'^2 <zeta, y_i + y_o>;
       c = k:  -mu^2 <zb, y_o + y_l> + mu mu' <1_3, y_i - y_j>;           c = l:  -mu^2 <zb, y_o + y_k> - mu mu' <1_3, y_i - y_j>;
   each equals rho m_c with rho = r_20 mu^2 + r_11 mu mu' + r_02 mu'^2 (the t^2-coefficient of theta_3/2).  (C2'pol) between Y and Z:
       mu <zeta, 2y_i - s> = 2 m_i Th,  -mu <zeta, 2y_j - s> = 2 m_j Th,  mu' <zb, 2y_k - s> = 2 m_k Th,  -mu' <zb, 2y_l - s> = 2 m_l Th,  0 = 2 m_o Th.
   Coordinates in V: basis zeta, zb, h := (1,1,1,-3); <zeta,zb> = 3, <h,h> = 12, other products 0; <1_3, x zeta + xb zb + eta h> = 3 eta.
   Up to exchanging zeta and zb (a row permutation) there are three placements of the pairs.
   (II') {i,j} = {a,b}, {k,l} = {c,n}, o = n'.  mu^2: (i) gives r_20 = 0, then <zb,y_n+y_n'> = <zb,y_n'+y_c> = <zb,y_c+y_n> = 0, so
     <zb,y_c> = <zb,y_n> = <zb,y_n'> = 0.  mu mu': (o) gives nothing, (l = n) gives <1_3,y_a-y_b> = 0, then (k = c) gives r_11 = 0 and (i)
     gives <1_3,y_c - y_n> = 0.  mu'^2: (k) gives r_02 = 0, then <zeta,y_a> = <zeta,y_b> = <zeta,y_n'> = 0.  (C2'pol): column n: <zb,s> = 0;
     column c: Th = 0; column a: <zeta,s> = 0.  So S lies in C h: q <= 1.  For Y in N: y_n' is orthogonal to zeta, zb and isotropic, so 0;
     y_n in C zb (the isotropic line of column n), y_c = xb_c zb + eta_c h, y_a = x_a zeta + eta_a h, y_b = x_b zeta + eta_b h, and
     <1_3,y_a - y_b> = <1_3,y_c - y_n> = 0 with sum_j y_j = 0 give eta_c = 0, eta_a = eta_b = 0: N = N_0.  dim K <= 1 + 2.
   (II'') {i,j} = {a,n}, {k,l} = {b,n'}, o = c.  mu^2: (i = a) gives r_20 = 0, then <zb,y_b> = <zb,y_c> = <zb,y_n'> = 0.  mu'^2: (k = b)
     gives r_02 = 0, then <zeta,y_a> = <zeta,y_n> = <zeta,y_c> = 0.  mu mu': (o = c) gives r_11 = 0, then <1_3,y_b - y_n'> = <1_3,y_a - y_n> = 0.
     (C2'pol), columns n, n': <zeta,s> = <zb,s> = 0: q <= 1.  For Y in N: y_n in C zeta, y_n' in C zb, y_c = eta_c h, y_a = x_a zeta + eta_a h,
     y_b = xb_b zb + eta_b h, and the 1_3-relations give eta_a = eta_b = 0, hence eta_c = 0: N = N_0.  dim K <= 3.
   (II) {i,j} = {a,b}, {k,l} = {n,n'}, o = c.  mu^2: (i) gives r_20 = 0, then <zb,y_n> = <zb,y_n'> = <zb,y_c> = 0.  mu mu': (o) gives
     r_11 = 0, then <1_3,y_n - y_n'> = <1_3,y_a - y_b> = 0.  mu'^2: -<zeta,y_a+y_b> = r_02 m_c, -<zeta,y_b+y_c> = r_02 m_a,
     -<zeta,y_a+y_c> = r_02 m_b; adding, <zeta,y_a+y_b+y_c> = 0, so <zeta,y_j> = r_02 m_j (j in P).  (C2'pol): column c: Th = 0; columns a, b:
     <zeta,y_a> = <zeta,y_b> = <zeta,s>/2; column n: <zb,s> = 0.
     If m_a != m_b: r_02 = 0, <zeta,s> = 0, S in C h, q <= 1; for Y in N: y_n, y_n' in C zb, y_c = eta_c h, y_a = x_a zeta + eta_a h,
       y_b = x_b zeta + eta_b h, eta_a + eta_b + eta_c = 0 and (C2') 12 eta_j^2 = vartheta m_j.  If vartheta is not == 0 on N the three
       linear forms eta_j are proportional to one form with coefficients gam_j, gam_j^2 = k m_j, sum gam_j = 0 = sum gam_j^2, so gam is a
       multiple of (1,w,w^2) or (1,w^2,w) and m is isotropic: excluded.  So eta_j = 0 and N = N_0: dim K <= 3.
     If m_a = m_b (= 1, m_c = -2): s = s_1 zb + s_2 h, and every Y in K is
         y_a = x zeta + (s_1/2) zb + eta_a h,  y_b = -x zeta + (s_1/2) zb + eta_a h,  y_c = -s_1 zb + eta_c h,
         y_n = xb_n zb + eta_n h,  y_n' = (s_1 - xb_n) zb + eta_n h,      2 eta_a + eta_c + 2 eta_n = s_2,
       and (C2'): eta_n (eta_n - s_2) = 0,  12 eta_a (eta_a - s_2) = vartheta,  12 eta_c (eta_c - s_2) = -2 vartheta.  Solving (linear forms):
       eta_n == 0 and (eta_a == 0 or eta_a == 2 s_2/3), or eta_n == s_2 and eta_a == c s_2 with 3c^2 + 2c + 1 = 0; in every case eta_a,
       eta_c, eta_n are multiples of s_2, so K lies in a 4-dim space parametrised by (x, xb_n, s_1, s_2).  If dim K = 4, K contains the
       elements with x = s_2 = 0, s_1 = 1: Y = zb l^T, l = (1/2, 1/2, -1, xb_n, 1 - xb_n), for every xb_n.  But T_n(Y) = 3 e_3(1/2,1/2,-1,1-xb_n)
       = -3/4 - (9/4)(1 - xb_n) and T_n'(Y) = -3/4 - (9/4) xb_n cannot both vanish.  So dim K <= 3.   QED
   CONSEQUENCE for the residual kinds: in (R3), (R4) the doubly centred part N contains neither a type I plane chi_1 (x) Lam_M nor a type II
   plane (in any position and after any row permutation).  What is left there: N on which vartheta is not identically 0, the g = 1
   spaces v (x) Lam with tau(v^3) != 0 (blueprint A1 with defect), and type IV-like configurations.

## LOG
STATUS 14:17: started; read BRIEF (+UPDATE, UPDATE 3), NOTES-zeros. Re-deriving reduction (i) and Lemma SL by hand first.
STATUS 14:20: hand re-derivation of every step done once (reduction, C2/C3/C4 column forms, dim N <= 2, q=3 => N=0,
 completeness of types I-IV, exclusions I-IV): no hole found so far; two imprecisions in the write-up located
 (type III uses a coefficient that can vanish when e_2(n) = 0 -- repaired by the write-up's own closing remark;
 type II "t mu'^2 coefficient of C3_a" is only valid in the normalised w-form -- the clean statement uses the deletion of the
 inactive column). Now numerics.
STATUS 14:26: TASK 1 done (verifyfl/test1.py): reduction L = F_r (+) L' confirmed on L080 (free col 4), ex1, ex2, ex3, s-family
 (s = 0.6+1.4i, 4, 0), 4x2 family member, R3: dim L' = 3, strong-level residual <= 1e-12, (q,d) = (3,0)/(1,2)/(2,1); negative
 control L9^T fails only through deletion-P_4. All identities used in my re-derivation hold at random points to 3e-14
 (verifyfl/test2.py, 33 identities). Next: coefficient checks of the exclusions, type II root count, LM with calibration.
STATUS 14:32: step-specific numerics done (verifyfl/test3.py, lm.py, lmrun.py, ext.py, ext3.py), all consistent with the claim:
 - type II: Newton finds all 17 affine solutions of tau(v v'^2) = tau(v^2 v') = 0 on the conic (5 diagonal, 12 off-diagonal);
   exactly 8 of the 12 have perm[v,v,v',v'] = 0 and these are the 4 common-zero-row pairs (x2 orders); the other 4 (a = 0)
   have perm = -128. Point at infinity excluded (perm = 8).
 - all closed forms used in the exclusions of types I, II, III, IV match brute-force P_3/P_4 of deletions to 1e-12.
 - LM (Grassmannian chart, my own code): strongly level spaces of dim 1, 2, 3 found from random starts; DC planes found are
   type II (4x) and type I (1x) only; random-start negatives at dim 4 / DC dim 3 are UNCALIBRATED (the relaxed P_2,P_3-only
   system, which has solutions, is also missed from random starts) -- not used as evidence.
 - CALIBRATED extension tests (fixed F, one new vector; passes the calibration that zeros/extsl.py failed):
   type II plane: 7/16 starts converge, ALL to N + C (1,1,1,-3)^T e_4^T (row-sum direction non-isotropic, as the proof needs);
   type I plane: 7/16 converge, ALL inside chi_1 (x) C^M (row sum in C chi_1);  R = chi_1 (x) C^M: 0/12 with P_4, 6/6 without P_4;
   every known 3-dim strongly level space (8 examples + 2 LM hits): a random plane of it re-extends (5-6/6), the space itself 0/10.
 Now writing the clean proof.
STATUS 14:38: blueprint S0-S11 written above and re-read line by line against my derivation (all formulas in S4-S8 rechecked,
 signs and coefficients match test2/test3 closed forms). Verdict: Theorem FL VERIFIED. Remaining time: extra adversarial checks.
STATUS 14:41: extra adversarial numerics (verifyfl/dc2more.py, extdc.py): 35/60 random LM starts give DC strongly level planes:
 34 x type II (k = 4, g = 2, pattern (2,2), always with a zero row; all four rows occur), 1 x type I (k = 3, g = 1); no type III/IV,
 no plane with a column of rank 2. DC one-vector extensions of the type I plane: 0/14 with P_4, 8/8 without P_4 (calibrated:
 P_4 is what caps dim N at 2); of the type II plane: 0/14 (and the calibrated search in the full column-centred ambient finds
 only the non-DC extension). Quick independent check of zeros' CA principle (RESULT 2, not needed for FL): derivation is
 correct (minor permanents off K vanish by Frobenius-Koenig since the surviving zero block has p'+q' >= 5 > 4; s^4 coefficient
 of the first-order condition gives L perp grad P_5(x); <grad P_5(x), J> = P_4(x) = 0).
STATUS 14:48: exact checks (test5_exact.py, test6_exact.py: all differences exactly 0) and the classification-free structured
 search (flag.py: (2,1) 10/12, (1,2) 1/10, (2,2) 0/40) done. FINAL: Theorem FL verified; blueprint S0-S11 above.
 Best next step: (1) formalise S1-S9 in Lean as a stand-alone lemma (the case analysis is finite; S10 lists the identities;
 hardest parts for Lean: the g-classification over 5 columns and the two WLOGs); (2) for the gap itself only free-line-free
 level spaces of dim >= 8 remain; the corollary "L_r strongly level for some row or column r => dim L <= 7" is the form to
 aim at (show that in a 9-dim level space some L_r is strongly level, e.g. via zeros' CA2).
STATUS 15:49 (round 2): new task (DI_5) at e = 1 received; read BRIEF UPDATE 4-6 and NOTES-rows (R1-R9, sections D, DI).
STATUS 16:05: Lemma EQ (any m) proved and checked on the examples; symmetrised normal form for m = e_a - e_b derived and checked;
 cases q = 3, q = 2 nondegenerate, dim zeta = 2 and dim Nbar = 3 of a hypothetical (5,1) excluded by hand; new exact (4,1) example found.
STATUS 16:20: last case (q, dim Nbar, dim zeta) = (2,2,1): sub-cases (N-a), (N-b), (c1), (c3), (c2-i), (c2-ii) excluded by hand; (c2-iii) reduced
 to (R'), closed numerically. Global LM with m fixed: (3,1) 9/10, (4,1) 9/61, (5,1) 0/84.
STATUS 16:30: section DI5 (DI5.0-DI5.6) and RESULT ROUND 2 written; error-catching test di_test5 passed on 22 two-column spaces. Round 2 final.
STATUS 16:33: the last sub-branch (R') is now PROVED (exact resultant (F1) + hand classification (F2)); Theorem TC5 is fully rigorous.
STATUS 16:36: fourth exact (4,1) example and calibrated extension tests added (di_test6.py). Round 2 final.
STATUS 17:38 (round 3): task received (split case of (5,1)); read BRIEF UPDATE 7-8 and stage3 N2-h.
STATUS 17:50: THEOREM SPLIT proved (thetahat = kappa * mu for non-isotropic m, 3 lines via the symmetric 5-linear form) and checked on 24 split
 examples; THEOREM FS (fully split in one row, any e) proved; Lemma HYP; searches with fixed general m running.
STATUS 17:58: R3.4-R3.7 written (isotropic counterexample, reduction to (NS4')/(K4), quadratic normal form, N2 criterion, numerics); RESULT ROUND 3 at top.
STATUS 18:05: Theorem TS (two-row split, e = 2) proved and checked; isotropic m: NEW split (4,1) spaces with ker kappa not strongly level found
 and verified (7-dim level, 1.7e-13); they do not extend to dimension 5 (0/60 each).
STATUS 18:15: column-centred spaces with good m: exist in dim <= 3, do not extend (0/56); isotropic (5,1): 0 of about 460 starts. Round 3 final.
STATUS 18:33 (round 4 started 18:20; logged late): analysis of the principal stratum (ker kappa containing a strongly level H with s(H) = V); normal form z_j = m_j((kappa/4)1 - 2B_j f) checked on 18 split (4,1) spaces.
STATUS 18:46: (I2) two-slot pairing for isotropic split found to be a consequence of the linear terms (no new information). Theorem PR3 proved by hand (no principal (5,1) for non-isotropic m with 3-support); formula checked 1e-14; isotropic N explicit, no extension 0/60.
STATUS 18:58: N-problem searches for |P| = 4, 5 (r4_n2.py) and Gr(4,15) searches for (SL_m) done; Lemma QB checked on 30 spaces. Section DI5-R4 and RESULT ROUND 4 written.
STATUS 19:07 (round 4 final): last numerics recorded (Gr(4,15) control rate only 3/82: those negatives are weak; climbs from C chi_1 mbar^T stop at dim <= 3). Rigorous this round: QB, PS, PR-RED, PR3, R4.2, R4.6. Numerical only: R4.5 remarks (i)-(ii), R4.7. Not achieved: (DI_5) at e = 1 (open: (o1), (o2) of R4.8); nothing new for (6,2), (7,3).
NOTE (process): the round-4 STATUS lines above were all written from 18:59 on (the 15-minute rule was not kept between 18:20 and 18:59).
STATUS 19:18 (ROUND 5 started 19:14, budget 100 min -> about 20:54; target (SL_m)): blueprint S3-S8 re-read; setting up the defect versions (Lemma C', pencil b_j^*g = s^*g + 4 m_j vartheta, types (q,d) with q + d = 4). First findings: for q = 3 the DC element Z_* vanishes on neutral columns; pencil counting alone cannot exclude type (3,1).
STATUS 19:30: new rigorous bricks for |supp m| = 3: Lemma 3C (a column-centred space supported on the three columns of P has dim <= 3, any m), Lemma NP (DC part supported on P: dim <= 2 for non-isotropic m, types I' and V), top-degree linear constraints on the neutral columns; type (3,1) with Z_* = chi_1 l^T, e_2(l) != 0 excluded. New exact planes verified (r5_checks.py). COMPUTE-verifyfl.md written for the 24-core machine (requests A-E).
STATUS 19:42: section DI5-R5 (R5.1-R5.8) and RESULT ROUND 5 written: Theorem SL3-RED reduces (SL_m) for non-isotropic 3-support m to the residual kinds (R1)-(R4); request F added to COMPUTE-verifyfl.md. Continuing with (R4)/(R3).
STATUS 20:00: R5.9 added: Props I-ALL and II-ALL (blueprint type I and type II planes never lie in a 4-dim K for |supp m| = 3; coefficient identities checked numerically, r5_propII.py); numerics: typed Gr(4,14) search fails even on the two-column control (0/34), climbs from the type II plane are reliable (control 3/3).
