# NOTES-dc5 (role dc5: upper bound for 5x5 DOUBLY CENTRED level spaces)

## !!! RESULT 12:45: a 4-DIM DOUBLY CENTRED LEVEL SPACE EXISTS at n = 5 (DC max >= 4, not 3) !!!
  K = { u p^T + conj(u) q^T :  p in span(chi_1, chi_4),  q in span(chi_2, chi_3) },
  u = (1, z^2, z, 0, 0), z = e^(2 pi i/3);  chi_k = (w^(k j))_{j=0..4}, w = e^(2 pi i/5).
  Supported on rows 0,1,2 (a 3 x 5 block).  Proof: P_4 = P_5 = 0 (only 3 nonzero rows); DC
  (sum u = 0, sum chi_k = 0) so P_1 = 0, 2P_2 = p_2, 3P_3 = 2p_3 (L_gct_105/106);
  p_2 = (Σu²)(Σp²) + 2(Σ|u|²)(p·q) + (Σū²)(Σq²) = 0 since Σu² = 0 and p·q = 0 (χ_a·χ_b = 5[a+b≡0]);
  p_3 = (Σu³)(Σp³) + 3(Σu)(Σp²q) + 3(Σū)(Σpq²) + (Σū³)(Σq³) = 0 since Σ_j p_j³ = Σ_j q_j³ = 0
  (no 3 of {1,4} or of {2,3} sum to 0 mod 5) and Σu = 0 (u_i ū_i = 1).  Found by LM in the
  column-graded family (dc5/graded.py, type (1,1,1,1)), fresh-point check 2e-13.
  Consequences: methods' (C*) (m + 2k <= 2n-3) is FALSE; "DC <= 3" is FALSE; L157 (3 x q
  row-centred <= q-1) is tight at q = 5.
  EXACT CHECK: dc5/cyc.py (Z[x]/Phi_15; all P_k vanish on a unisolvent set; checker sanity-tested).
  CORRECTION (13:12): with the EXACT basis, K has DC first-order tangent 16, full 5x5 first-order
  extension 10, Hessian dims Y = (7,8,8). The earlier "tangent 0 / ext 5 / (7,8,9)" came from the LM
  basis level4_1111.npy, which is only ~1e-7 accurate (residual ~ error^2: singular solution), so the
  1e-8 rank threshold misread it. K is numerically ISOLATED (perturbations <= 0.1 in all of U return
  to it) but not first-order rigid. Seeded full-space extension of K: no level space of dim >= 6 found.
  n = 4 ANALOGUE (EXACT, dc5/cycn.py over Z[x]/Phi_12): u = (1,z^2,z,0), chi_k = (i^(kj)):
  K_4 = u(x)span(chi_2) + conj(u)(x)span(chi_1,chi_3) is a 3-dim 4x4 DC level space, so L_gct_216
  (4x4 DC <= 3) is TIGHT and the old "n=4 DC max 2" numerics were wrong. (full ext dim 5: no LS(4)=6.)
  GENERAL MECHANISM: on 3 rows with u = cube roots, t = u p^T + ū q^T is level iff p.q = 0 and
  Σ_j p_j^3 + Σ_j q_j^3 = 0 (P4 = P5 = 0 trivially; Σu = Σu² = 0, Σ|u|² = 3, Σu³ = 3).  Character
  choice p in span(chi_S1), q in span(chi_S2): need S1+S2 ∌ 0, no 3-multiset of S1 or of S2 sums to 0
  mod n. Max |S1|+|S2| (dc5/threerow_n.py): n=4:3, 5:4, 6:3, 7:4, 8:6, 9:4, 10:8, 11:8, 12:9, 13:8.
  Gluing 3x5 and 5x3 blocks (L_gct_110) gives DC >= n - O(1) for general n (dim 8 at n = 8).
  3-ROW CLASSIFICATION (exact except the split step): every 3-row DC matrix is u p^T + ū q^T; all LM
  solutions split as u(x)W1 + ū(x)W2 (numerical), and then W1, W2 are LINES ON THE CLEBSCH DIAGONAL
  CUBIC SURFACE {Σx = 0, Σx³ = 0} with W2 = W1^perp (planes cannot lie on it). Of its 27 lines the 15
  rational ones have polars off the surface; the other 12 form ONE S5-orbit (stabiliser D5), closed
  under polarity (checked numerically, exact in principle). Hence every 4-dim 3-row DC level space is
  S5 x S5-equivalent to K (modulo the split step). The 'generic' LM solutions are column permutations
  of K (verified: W1 is an S5-image of span(chi_1,chi_4)).
  (old text:) LM in the 8-dim 3-row ambient finds 4-dim solutions from random starts;
  generic members have DC tangent 16, DC first-order ext 8 (P2..P5), full first-order ext 10, but
  seeded LM: full level extension to dim 5 converges (7e-13) but the solution DRIFTED to a space with
  NO DC member (row/col-sum map injective), so it says nothing about K4; dim 6/7/9 stall (0.08/0.5/2.4);
  DC extension to dim 5 stalls (0.28). Random LM in the full DC space (25 starts, d=4 level) finds
  NOTHING, although this family exists: LM negatives at n = 5 are worthless.
  Lemma (B) is FALSE: K has Y3 = 7, Y4 = 8 < 3d-2 = 10.
  Graded/character searches: Z4xZ5 on 4 rows gives at most 3 (P5 automatic there).

## RESULT (updated 12:30) -- no proof of d <= 4; the p2/p3 route is DEAD; exact examples fix the targets
U = 5x5 DC matrices (16-dim, <s,t> = sum s_ij t_ij nondegenerate on U), K ⊆ U, d = dim K,
pi = orthogonal projection C^25 -> U, A_t s = pi(t*s), H^k_t = Hessian operator of P_k at t.
(E1) EXACT: p2 = p3 = 0 allows d = 6, so the brief's "L061-style -> 16/3 -> 5" is FALSE (not just
     unproved). Abelian weight construction (L_gct_119 mechanism): g = (sigma,tau) acting by
     t -> t(sigma i, tau j); the DC part of the sum of z^e-eigenspaces, e in E, kills P_k whenever no
     k-multiset of E sums to 0 mod N (torus invariance of P_k). DC p2p3 spaces of dim 6:
       sigma=(01234), tau=(012)(34), N=30, E={2,3,4,6,8,9};  sigma=(0123), tau=(01234), N=20,
       E={1,2,3,11,12,13}   (dc5/weight.py, wsearch.py; |p2|,|p3| polarizations ~1e-16).
     Exhaustive over all pairs of S5 cycle types (wsearch.py): max DC dim = 6 (p2p3), 4 (P2..P4),
     3 (level). So: true p2p3 max is in [6,8]; random LM (max 5) missed the 6.
(E2) EXACT: P2..P4 allow d = 4: Vxv = {w v^T : sum w = 0}, v = (1,w,..,w^4) (P_k(xy^T) = k! e_k(x)e_k(y),
     L089), plus the weight spaces (32,5,E={2,3,4,6}) and (4,5,E={1,2,3,4}). P5 != 0 on all of them.
     => any proof of DC <= 3 must use P5; 4 is the best P2..P4 can give.
(E3) Hessian-image method (rigorous, elementary): K ⊥ H^k_t K for t in K (coefficient of ab in
     P_k(t+as+bs') = 0), and K ⊥ RC, so with Y_m := K + sum_{k<=m} sum_t H^k_t K (subset U):
         d <= 16 - dim Y_m.                                                    (*)
     Measured dim Y_m (single generic t; all-t spans equal in the one case checked, level weight (32,5)):
       Vxv (d=4,P234): Y3=8, Y4=12;   weight P234 d=4: Y3=7, Y4=10;   weight p2p3 d=6: Y3=10 (=16-d);
       level weight (4,5,{1,2,3}) d=3: 5, 8, 9;  level weight (32,5,{2,3,4}) d=3: 5, 7, 8;
       level Wxv d=3: 6, 9, 10; random p2p3 / P234 spaces: 2d, 3d, min(4d,16).
     So the growth lemmas consistent with ALL data are
       (A) p2=p3=0  => dim Y3 >= 2d-2  (gives d <= 6, tight)
       (B) P2..P4=0 => dim Y4 >= 3d-2  (gives 4d <= 18, d <= 4, tight at the weight spaces)
     while a UNIFORM P5 lemma "Y5 >= 4d-c for all d" needs c >= 4 (level weight space (32,5): d=3,
     Y5 = 8 = 4d-4) and then only gives 5d <= 20, d <= 4; DC <= 3 via (*) would need a d-dependent
     deficit (Y5 >= 13 at d = 4), i.e. structure beyond counting. Lemma (B) is the natural target for "DC <= 4"; it is a Kneser/Cauchy-Davenport type
     statement in the NONASSOCIATIVE algebra (U, ∘) with AP-like extremal cases (weight spaces), so
     L065 does not apply directly. The naive versions (>= 2d, >= 3d, single-t independence) are FALSE.
(E4) DEAD: "X = 1+K+K*K with X ∩ RC = C1" (fails: X ⊇ RC in examples); "p2,p3 => d <= 5";
     "P2..P4 => d <= 3"; random LM as evidence at n=5 (missed Vxv and the 6-dim p2p3 spaces).
Fourier picture (may help): U ≅ C[Gamma], Gamma = (Z5*)^2; t∘s = pi(t*s) is convolution
     restricted to Gamma (chi_a∘chi_b = chi_(a+b) if a+b in Gamma, else 0); <chi_a,chi_b> = 25 [a+b=0].
     This is a NONASSOCIATIVE algebra, so Kneser (L065, e-transform) does not apply directly.

(Log below; lines before 12:26 are partly SUPERSEDED by RESULT above.)
STATUS 12:07: started; reading L_gct_216, L163, L065.
STATUS 12:10: LM: dim5 DC with p2=p3=0 EXISTS (res 8e-13) so P4/P5 needed; dim 6 not found. P2..P4 d=5,d=4 not found (res .6/.19).
STATUS 12:14: KEY CORRECTION to brief: the "L061-style 16/3 -> 5" bound is NOT a valid argument as
 stated. K ⊥ X := 1+K+K*K and K ⊥ RC (9-dim row/col indicators) give d <= 25 - dim(X+RC), and
 Kneser gives dim X >= 2d+1; the 16/3 needs X ∩ RC = C1. FALSE in practice: the 5-dim DC space
 with p2=p3=0 found by LM (dc5/sol_d5_k23_s1.npy, res 8e-13) has dim X = 20 and X ⊇ RC
 (dim X∩RC = 9). With X ⊇ RC the count only gives 3d <= 24 (d <= 8, same as L061 with M=25).
 Equivalent correct form of the 16/3 claim: in U = DC (16-dim) with π = orthogonal projection,
 need dim(K + π(K*K)) >= 2d  [= Kneser for the NONASSOCIATIVE algebra U = A⊗A, A = (C^5_0, x∘y =
 π(x*y))]; not proved anywhere. So the rigorous DC bound from p2,p3 is still 8.
 Numerics (dc5/srch.py, LM): p2=p3=0: d=5 found, d=6 not (10 starts). P2=P3=P4=0: d=3 found
 instantly, d=4 and d=5 NOT found (10 starts each). So P5 seems unnecessary for d<=3.
STATUS 12:17: IMPORTANT: P2..P4 alone do NOT give d<=3: V⊗v = {w v^T : w in C^5, sum w = 0},
 v = (1,ω,ω²,ω³,ω⁴), ω = e^{2πi/5}, is a 4-dim DC space with P2=P3=P4=0 (P_k(wv^T)=k! e_k(w)e_k(v),
 e_1..e_4(v)=0), P5 = 120 e_5(w) ≠ 0. LM (40 starts) missed it -> random LM is unreliable here;
 earlier "P2..P4 d=4 not found" is NOT evidence. Any d<=3 proof must use P5; d<=4 might follow
 from P2..P4 (open: is there a 5-dim P234 DC space? testing seeded from V⊗v).
STATUS 12:26: RESULT section written; next: try to prove Lemma A/B in special cases.
STATUS 12:27: extra checks. (i) Vxv is an ISOLATED 4-dim P2..P4 space: Grassmannian tangent
 dim 6 at first order (dc5/tangent.py) but LM restarted from perturbations 0.01..0.06 returns exactly
 to Vxv (principal cosines 1,1,1,1; dc5/fam.py); expected dimension of 4-dim P234 spaces is 48-65 = -17.
 (ii) Tangent dims at random solutions match expected dims (3-dim P234: 8 = 39-31; 5-dim p2p3: 5 = 55-50).
 (iii) Orthogonality K ⊥ H^k_t K checked numerically on Vxv (k=3,4) and Wxv (k=3,4,5), ~1e-10;
 fails for Vxv at k=5 as it must (P5 != 0).
 (iv) Hopf-type count (rigorous): beta(t,s) = [pi(t*s)] in Q = (K^perp∩U)/K (dim 16-2d) is a symmetric
 bilinear map; if it had no zero divisors then 2d-1 <= 16-2d, i.e. d <= 4. But zero divisors exist
 already in Vxv (a∘b = 0 for a = v, b = conj(v)), so this cannot be used without structure theory.
 Formalization: (C3) orthogonality = coefficient extraction (helpers TaylorOnSpace/OrderConditions,
 MkPol polarization) + dot-product rank-nullity (as in L092/L163): moderate. Vxv example: L089 +
 e_k(5th roots of unity) = 0: easy-moderate. Lemma A/B (independence): no formalizable idea; hard.
STATUS 12:30: RESULT rewritten after finding exact 6-dim p2p3 DC spaces (weight constructions).
STATUS 12:33: more tests. Lemma (A) "Y3 >= 2d-2" holds on all 126 coordinate subspaces of both
 6-dim p2p3 weight spaces (worst deficit Y3-2d = -1 at d=3,4,5, -2 at d=5,6); Lemma (B) "Y4 >= 3d-2"
 holds on all coordinate and random subspaces of the three 4-dim P234 examples (dc5 one-liners).
 Weight spaces: first-order ext dims 6 (P234, d=4) and 7/8 (level, d=3) but seeded LM extensions
 (to 5-dim P234 / 4-dim level, 12 starts each) all stall at res 0.14-0.39.
 Exactness of (E1),(E2): row/col permutations preserve every P_k, pi commutes with them, so the DC
 part of a sum of z^e-eigenspaces of g=(sigma,tau) lies in that sum; monomials of P_k of nonzero
 total weight vanish by invariance -> P_k = 0 if no k-multiset of E sums to 0 mod N. Exact over Q(zeta_N).
 Files: dc5/srch.py (LM, any subset of P_k), ext.py (seeded LM), extdim.py (first-order extension),
 tangent.py (Grassmannian tangent), hess.py (Hessian images, Y_m), lemA.py, weight.py, wsearch.py
 (exhaustive abelian weight search over S5 cycle-type pairs), fourier_sets.py, tst.py.
STATUS 12:33: finished; final report sent. Best next step: prove Lemma (B) (gives DC <= 4) or classify 4-dim P2..P4 DC spaces.
STATUS 12:39: NEW TASK (75 min): classify 4-dim P2..P4 DC spaces; P5 on them; Lemma (B) via Fourier.
STATUS 12:47: the 4-dim DC level space K (3-row block) is EXACTLY verified (dc5/cyc.py: exact
 arithmetic in Z[x]/Phi_15, all P_k vanish on a unisolvent set; checker sanity-tested on Vxv: P5 fails).
 [CORRECTED 13:12: these K invariants were computed on an inexact LM basis; see CORRECTION at top]
 K is RIGID: DC Grassmannian tangent for P2..P5 = 0 (isolated reduced point), P2..P4 tangent 10.
 First-order extension of K inside ALL 5x5 matrices (P1..P5): dim 5 -> every level space containing
 K has dim <= 5. Hessian dims of K: Y3=7, Y4=8, Y5=9 -> growth Lemma (B) "Y4 >= 3d-2" is FALSE (d=4,
 Y4=8): block-supported spaces violate it (P4,P5 vanish trivially on 3 rows). (B) is DEAD as stated.
 Column-graded search (dc5/graded.py, gradall.py): 4-dim P234 types (0,0,0,4),(0,0,3,1),(0,1,1,2),
 (0,1,2,1),(0,2,1,1),(1,1,1,1) all occur; with P5 only (1,1,1,1) (= K) found. 5-dim graded P234: none
 (13 types x 6 starts).
STATUS 12:48: !!! generic 4-dim 3-row DC level spaces (LM, rows 0-2) have FIRST-ORDER EXTENSION DIM 10 in the full 5x5 (P1..P5): candidates for a 9-dim level space. Testing seeded extension now (dc5/fullseed.py).
STATUS 12:57: notes updated with n=4 analogue, 3-row mechanism, family data, Lemma (B) dead.
STATUS 13:00: STABILIZER PATTERN (dc5/stab.py). Define Stab_R(K) = {row functions f : pi(f*K) ⊆ K},
 Stab_C likewise (constants always in). M_f := pi∘(f*) = (P_V D_f) (x) I on U = V(x)V.
   3-row K (graded and generic): (3,1);  Vxv: (5,2);  weight P234 / p2p3-6 / level-3 spaces: (2,1) or (3,1);
   random LM solutions (p2p3 d=4,5; P234 d=3): (1,1) = trivial.
 => every example that VIOLATES the naive growth bounds (Y3 >= 2d, Y4 >= 3d) has a nontrivial row or
 column stabilizer; every random one has trivial stabilizers and satisfies Y_m = min((m-1)d, 16).
 PROPOSED ARCHITECTURE for DC <= 4 (Kneser with stabilizer, unproved):
  (K1) trivial Stab_R and Stab_C  =>  dim Y4 >= 3d - c (c small)  =>  d <= 4 by (*).
  (K2) nontrivial Stab: K is invariant under A_f (x) I (A_f = P_V D_f self-adjoint on V), so K splits
       along generalized eigenspaces of A_f.  For f = 1_S (row block S): V = V_S + V_{S^c} + C y,
       eigenvalues 1, 0, |S^c|/5, y = |S^c| 1_S - |S| 1_{S^c}; K = (K∩V_S(x)V) + (K∩V_{S^c}(x)V) + (K∩y(x)V);
       the y-part is 0 (P_k(y w^T) = k! e_k(y)e_k(w), e_2..e_5(y) != 0 force e_2..e_5(w) = 0, so w = 0);
       S-part = DC level on |S| rows: <= 4 for |S|=3 (L157), <= 2 for |S|=2 (isotropy), 4x5 open.
       Crude sum gives 6 for |S| = 3; the cross conditions between the parts must be used to get 4.
  General (non-indicator) f in the stabilizer still to be handled.
STATUS 13:07: graded searches with row vectors restricted to rows R (dc5/graded_rows.py):
 R = {0,1,2}, total 4: only type (1,1,1,1) (= K) found; R = {0,1,2,3}, total 4: (1,1,1,1) found in 4 s;
 total 5 (P5 automatic on 4 rows): all types fail (12 starts x 40 s for the (2,1,1,1)-orbit, res ~7.5).
 (3,2) row-block case of (K2), exact cross conditions for K = K_S + K_T (S = 3 rows, T = 2 rows,
 K_T = {[x;-x]: x in X}, X isotropic in V): P2, P3 have NO cross terms (disjoint supports, zero column
 sums); P4 cross term (bidegree 2,2) = 0  <=>  Σ_{r in S}(a_r·x)(a'_r·x') = 3 Σ_j (Σ_r a_rj a'_rj) x_j x'_j
 (symmetrised); P5 (bidegree 3,2) = -2 Σ_{|C|=3} perm(a[S,C]) x_c' x_c'' (C^c = {c',c''}) = 0.
 Need: dim K_S + dim X <= 4 (unproved; seeded DC LM from K_S + 2-row directions stalls at 0.28).
STATUS 13:08: (a) 3-row 4-dim DC level spaces are RIGID inside the 3-row ambient (tangent 0 in G(4,8)) and distinct
 solutions differ by column permutations: ONE orbit (see 3-ROW CLASSIFICATION; the 'two orbits' claim
 was an artefact of the inexact LM basis). Generic ones are also isolated in the full DC level variety
 (perturbations eps <= 0.1 in all of U return to the same space; first-order tangent 16 is obstructed).
 (b) Row-block cross formulas verified numerically (1e-14): P2, P3 no cross terms; P4 cross =
 -(3/2)Σ_j c_j(a)c_j(b) + (1/2)||a b^T||^2 + (1/4)p2(a)p2(b); P5 = Laplace over 3+2 rows.
SUMMARY FOR COORDINATOR (task 2):
 (1) 4-dim P2..P4 DC spaces: NOT a short rigid list -- many graded types ((0,0,0,4)=Vxv, (0,0,3,1),
     (0,1,1,2), (0,1,2,1), (0,2,1,1), (1,1,1,1) up to chi_k -> chi_2k) plus all 3-row DC spaces (P4 = P5 = 0
     automatically). No continuous symmetry was used; isolation only checked numerically at samples.
 (2) P5 kills Vxv (exact: 120 e5(w)) and the weight spaces (numerical), but NOT the 3-row ones:
     DC LEVEL SPACES OF DIM 4 EXIST (exact). So "DC <= 3" is false; DC <= 4 is the sharp target.
 (3) Lemma (B) is false (3-row K: Y4 = 8 < 10); Hessian counting alone cannot prove DC <= 4.
     All violators have nontrivial row/column-function stabilisers -> Kneser-with-stabiliser architecture.
STATUS 13:13: split step partial: if K (4-dim, 3-row, level) projects isomorphically to both factors
 (K = graph of phi, a=b=0 case), then phi is skew-adjoint and c∘phi = -c (c = Σx³ on V); linear
 automorphisms of the Clebsch cubic are scalars x S5, so phi = mu*sigma with sigma^2 = -1 on V:
 impossible for a permutation. Mixed cases (0 < dim W1' + dim W2' < 4) not done.
 Task-2 finished; final report sent.
