# NOTES-leanfl (role: leanfl; round 1 16:38-18:05, round 2 18:13-19:15, round 3 19:16-)
## RESULT ROUND 15 (leanfl, 07:31-08:04 UTC) -- WORK ON L-gct-210 ABORTED BY KEVIN at ~08:04
##   * Certificate pipeline scoped (section CERTIFICATE PIPELINE below): RED-p core in Lean COMPILED (Tcert, 0 errors): valuation
##     subring B of C with p in B.nonunits (Mathlib), projective normalisation, unit_contra; chart certificates checked by
##     linear_combination over any CommRing, ~3 ms per term product (~20 s for CC34 chart 0123). Bottleneck = certificate generation
##     (Singular lift) for the msolve-hard tail (~8% of charts). Verdict: complete Lean proof = months, not weeks.
##   * Stage B: FLK_field (ab5e1e4d26) 7 errors (chart/spv_inj Fact, 5 TC5_* lemmas with /2, NeZero 5 over C) -> fixed; new
##     FLK_field 4f20faf49e and TrK11 6a9f290251 NOT YET COMPILED (old TrK11 d34ad9249a run not read). Upstream L_gct_152 copied
##     to lean/fl/kk152.part (not compiled, unused).
##   FILES (md5, status): lean/fl/FLq2.lean 11b60a129a COMPILED CLEAN (TC5_final + L_gct_210 axioms standard); lean/fl/FLq.lean
##     7a1f2e7aca (7 heartbeat timeouts, superseded by FLq2); lean/fl/FLK_field.lean 4f20faf49e not compiled; leanfl/TrK11.lean
##     6a9f290251 not compiled; leanfl/TrK0p.lean 388ad0fbd3 COMPILED CLEAN (160 s); leanfl/FLK_FL.lean 0d7f568f89, FLK_SLa
##     3cb27e8b31, FLK_SLb d7621ba33b, FLK_SLc 00b35573d2, FLK_SLd 3d17f8830d not compiled (fallbacks); leanfl/TrC0p.lean 465e974927
##     not compiled; leanfl/Tr11.lean 82f261fdf9, Tr13.lean 52065b9244 not compiled (covered by FLq2); leanfl/cert/Tcert.lean
##     e562ba8db2 COMPILED CLEAN; cert/Tcert2.lean 1153b8c1db, cert/Tcert3.lean 079faec787 not compiled; lean/fl/kk152.part f1a48f75ec.
## RESULT ROUND 14 (leanfl, 03:57-07:31 UTC; cut off 04:25-05:15 by the account limit)
##   TC5 COMPILES (over C): lean/fl/FLq2.lean (md5 11b60a129a, 16660 lines) -- exit 0, 0 errors, 0 sorry, 1418 s, peak 8.95 GB;
##   'PEqualNP.Outside.L_gct_210' and 'PEqualNP.Outside.L_gct_210_aux.FL.TC5_final' both depend only on [propext, Classical.choice,
##   Quot.sound]. FLq2 = FLq + set_option maxHeartbeats 4000000 in on P4_c2_canon (p5f), F1_vprod (p5i), noline (p5o): the FLq rebuild's
##   7 errors were all per-declaration heartbeat timeouts (budget eaten by big certificates). FLq.lean kept as compiled (7a1f2e7aca).
##   SPEED FIXED: TrK0p rerun 0 errors, 160 s (was 1720 s) = C rate per line; cause was the failing (N : Kf) != 0 discharger inside
##   field/field_simp; now first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]. propR (FLK_FL error) passes.
##   STAGE B BOOKED: LEANFLK_FIELD (lean/fl/FLK_field.lean ab5e1e4d26, whole SL+FL port + C corollary, 45 min), LEANTRK11
##   (leanfl/TrK11.lean d34ad9249a, TC5 over Kf, 60 min), ~08:30-10:30 UTC. Fallbacks unbooked: FLK_FL 0d7f568f89, FLK_SLa..d.
##   Upstream reuse: local L_gct_214/215/216/217 checked -- over C, different hypotheses; none replaces an SL/FL/TC5 leaf or the port.
## RESULT ROUND 13 (leanfl, 03:01-~04:30 UTC) -- Stage A (TrK0p profile, FLK_FL) not yet run when this was written
##   TC5 IS CLOSED IN SOURCE: TC5_final : DefLine K mTC -> finrank K <= 4 (p5ad), no hypotheses left; compile pending
##   (FLq rebuild after Stage A; TrK11 = the same over Kf with (2,3,5 : Kf) != 0 and |Kf| > 20, no i needed).
##   (c1), all certificates sympy-checked:
##   * p5o noline (integral Singular certificates over Z; 7 avoided), p5p c1_plane, p5q c1_reduce (t3 v v v != 0 impossible;
##     otherwise the coefficient plane is Lambda345), p5r (D_N in C z; R = v (x) Lambda345 in K) -> C1RHyp.
##   * S8 run: p5s exists_iso_rs, p5ab exists_rad_rs (n0 = rs Y0 in the radical of S), p5t/p5u (C2/C2pol consequences),
##     p5v c1R_x3c, p5w c1R_b / c1R_v2n (t3 v v n0 = 0 => n0 = p v + r v^3, p r = 0), p5x pc_Qv13, p5y c1R_case_v3 (r-case),
##     p5z c1R_case_v_u (p-case, u = 0), p5aa pc_Qv12 / x3c_Qv12, p5ac c1R_W + c1R_case_v_final (fourth vector: kap_u = -q,
##     kap_j = q from X3c, then pc = -24 kap^2 q^4 != 0), p5ad C1R_proof, TC5_final.
##   Window-3 Tr11: same declarations as FLq plus two new small errors (Set.finrank vs span in omega; frame k0 = 3 rfl), fixed.
##   In Tr11 the whole (c2-iii) chain elaborated.
##   Port speed: no profile yet (TrK0p queued after leanzbf); nothing changed in the porter this round except the generic_t patch for
##   c1_reduce (hs argument).
## RESULT ROUND 12 (leanfl, 02:06-~03:35 UTC)
##   FIELD PORT, window 3: TrK0 (smoke test, 1468 lines) compiled with only 2 errors, both the syntax slip (X (Kf := Kf)) (n := 4) in
##   Vp_finrank (fixed in port.py: no outer parentheses before a named argument) -- i.e. the header, the Ii chain, generic_pt with the
##   |Kf| > 20 hypothesis, the cast patches, cast_two/cast_inj5/cast_succ_ne, the nz/zn/ne simp lemmas and the field fallbacks all
##   elaborate. No simp/norm_num call failed for lack of characteristic 0 in TrK0 (so far no silent char-0 step was found).
##   SPEED is the problem: 1720 s for 1468 lines (~30x slower per line than the C files); FLK_field/TrK11 were stopped by the coordinator.
##   The field-first sites in TrK0 are small scalar goals, so field alone probably does not explain it; field now has a cheap discharger
##   anyway. Stage A (booked after window 3): leanfl/TrK0p.lean (TrK0 + profiler, threshold 300 ms) and leanfl/FLK_FL.lean; the profile
##   decides the speed fix. Stage B files ready: FLK_SLa (SL_of, 2818 lines), FLK_SLb (HypS6, 1833), FLK_SLc (HypS7, 1472),
##   FLK_SLd (HypS8, 1729) -- SL split along FLk's own HypS6/7/8 structure -- and TrK11 (TC5, 8099 lines).
##   Porter fixes this round: binder shadowing detected in every signature group; shadowed names no longer pull a declaration into the
##   i-closure (the TC5 parts do NOT need i^2 = -1); builds are atomic (*.new + mv).
##   FLq (window 3, parts up to p5j): 1384 s, 17 errors in 7 declarations, all fixed now (see the STATUS line after 02:59); every other
##   block of rounds 8-11 COMPILED, including P4_k3, TC5_c3, P4_c2i, P4_c2ii, c2_plane, P4_c2_perm, TC5_main, F1_zero_row, c2iii_zero_row.
##   TC5 (C source; ported in TrK11):
##   * p5g TC5_main: C1Hyp -> C2iiiHyp -> DefLine K mTC -> finrank K <= 4 (the final dispatcher: P4_k3, parallelism split,
##     transports via swap 3 4 / swap 2 4, TC5_c3, P4_c2_canon). TC5 is ONE theorem modulo the two named sub-case hypotheses.
##   * p5h c2iii_zeta (D_N = zeta sub-case of (c2-iii) via L_slev + pattern23/G23); C2iiiLagHyp; TC5_main' : C1Hyp -> C2iiiLagHyp -> ...
##   * p5i (F1) as exact ideal membership (F1_zero_row; Singular lift, sympy-checked); p5j c2iii_zero_row.
##   * p5k uconst_0..3 and p5l F2_scalar: steps 3 and 4 of the Lagrangian sub-case (plan in the 02:38 STATUS line);
##     p5m c2iii_h, c2iii_ei: steps 5 and 6 (the two final contradictions).
##   * p5n c2iii_core, C2iiiLag_proof : C2iiiLagHyp, TC5_of_c1 : C1Hyp -> DefLine K mTC -> finrank K <= 4.
##     => (c2-iii) closed in source; TC5 rests on the single hypothesis C1Hyp (sub-case (c1), all three lines parallel). Next: (c1).
## RESULT ROUND 11 (leanfl, 01:10-~02:40 UTC; nothing compiled this round -- window 3 compiles leanfl/window_files.txt in order:
##   lean/fl/FLK_field.lean (TOP), leanfl/TrK11.lean, lean/fl/FLq.lean, leanfl/Tr11.lean)
##   A. FIELD PORT (coordinator's top target, for verifyfl R11.6 = SL and TC5 in char P1):
##   * lean/fl/FLK_field.lean (8006 lines, guard 0, project guard passes) = FLk (Lemma SL, Theorem FL, all of it) over a field Kf.
##     Generated, not hand-copied: leanfl/port.py (C -> Kf, abbrevs V4/M45/M55 take Kf, numeral facts as instances, Kf := Kf at
##     call sites of lemmas whose explicit arguments do not fix Kf, (norm := first | ring1 | field [nzN..]) for every
##     linear_combination / ring), leanfl/port_header.txt, leanfl/port_patches.json (15 hand patches), leanfl/buildK.sh.
##     Ported parts live in lean/fl/K/*.part (closure.py-testable: DIR lean/fl/K).
##   * HYPOTHESES (the explicit list): [Field Kf], NeZero (N : Kf) for N in {2, 3, 5} ONLY, plus
##       (i)  exists i : Kf, i^2 = -1                      (only where FLk used Complex.I: r3/spv/HypIIa/HypS6C chain),
##       (ii) every Finset of <= 20 elements of Kf misses a point (|Kf| > 20)  -- FLk's generic_pt used Infinite C
##            (Infinite.exists_notMem_finset); verify2's scan did not list it. Needed sizes: 5 (rows) and 20 (all entries).
##     Every other numeral is derived: nzN lemmas for N = 4,6,8,9,10,12,15,16,18,20,24,30,32,36,40,45,48,60,64,72,96,120,128,
##     144,256,288 (products of 2, 3, 5). So the characteristic must avoid exactly the primes 2, 3, 5; P1 = 2147483629 is fine.
##     Where 5 enters: (1/5) in the 120-normalisation, 120 != 0 (propR), injectivity of k -> k+1 on Fin 5 (roots5 Vandermonde:
##     cast_inj5, cast_succ_ne replace Nat.cast_injective / Nat.cast_add_one_ne_zero), S.card = 2 from (S.card : Kf) = 2.
##     7 is NOT needed (no field literal has the factor 7 in FLk); verify2's 7 must have been an N-literal.
##   * C versions kept as corollaries: SL_FL_C (Kf := C, i := Complex.I, |C| > 20 from Infinite). The final test theorem
##     states the char-p version (all Kf with the hypotheses above) AND the C statement of Lemma SL.
##   * TC5 blocks: leanfl/TrK11.lean (7531 lines, guard 0) = closure of all TC5 parts (rounds 7-11) over Kf with the needed
##     ported FLk/FLl/FLm blocks; same hypotheses (the round 7-11 parts add no new numeral: no literal with a prime > 5).
##   * Not decided yet (needs the compile): simp/norm_num calls that used CharZero silently. Mitigation: @[simp] nzN/znN lemmas
##     (N != 0, 0 != N) and neA_B (A != B for 1 <= A, B <= 6) so simp/norm_num close numeral contradictions as before;
##     every declaration using field gets set_option maxHeartbeats 800000 in. Expect a small error list in window 3.
##   B. TC5 (P4) progress (all source, compile pending in FLq):
##   * p5e.part c2_plane: in a (c2) configuration the coefficient map N -> (l3, l4, b) has 2-dim image with explicit generators.
##   * p5f.part P4_c2_canon: canonical (c2) dispatcher: det != 0 -> (c2-i) P4_c2i with (lam, mu) from Cramer; a = c b, c != 0 ->
##     (c2-ii) P4_c2ii; c = 0 -> (c2-iii) left as the explicit hypothesis Hiii. Remaining (P4): (c2-iii), (c1), placement
##     transports, final TC5 dispatcher.
##   C. Char note for verify2/verifyfl: the Lean TC5 route (rounds 8-11) uses only 2, 3 invertible (plus the field port facts
##     above); see the round-11 char-p note further down.
## RESULT ROUND 10 (leanfl, 00:23-01:05 UTC; nothing new compiled yet -- window 3 compiles window_files.txt = FLp.lean, Tr10.lean)
##   FLp.lean = FLo + R10 (p4c p4d p4e p4f p4g p4h p4i; 14070 lines, guard 0, no sorry); Tr10.lean = closure of R10 (5044 lines).
##   TC5 (P4): the configuration is K 5-dim, q = 2, dim Nbar = 2, zeta = C z (TC5_dims); new results:
##   * k = 2 active neutral columns is IMPOSSIBLE (P4_k2_all, all three placements via column permutations fixing the defect pair):
##       (N-a) one line (P4_Na): cubic gives tau(v^3) = 0; D_N is Q-isotropic with <v,E(d)> = 0 (DN_line), so D_N = C z (LAG_pair:
##             two independent such d contradict LAG_b); N'' = N cap {d = 0} is a 2-dim strongly level outer(v,.) space with only one
##             identically-zero column, contradicting A1cols.
##       (N-b) two lines: cubic gives the pair relation; by pair_rel the pair is chi_1-type or zero-row.
##             chi (P4_Nb_chi): F_v vanishes on D_N, d is injective on N (Qbar polarisation), dim D_N = 3 > 2 (Fv_nondeg).
##             zero-row (P4_Nb_zero): F_v = (tau(v^3)/4) l_v^2 on N; h = 1 - 2 e_{k0} spans the radical of F_v and F_w;
##             h in D_N gives zE(h) in K and perm[h,h,v,w] = 2<v,w> != 0 against (Z2); h notin D_N gives z in C h (contradiction).
##   * P4_k3: in the (P4) configuration all three neutral columns are active (lines v_2, v_3, v_4 all nonzero, realised).
##   * (c3) part 1 (P4_c3_Ez): three pairwise non-parallel lines and E(z) != 0 is impossible (three_iso_perp).
##   Shared: LAG_pair, DN_line/DN_pol/DN_on_z, Mv/Fv_nondeg (F_v nondegenerate iff all v_k != 0 -- simpler than the paper),
##   qbar_pol, X3c_gen2/3, hvec/Mv_ker/pc_hvec, dY_inj_two. Every certificate sympy-checked (leanfl/gen_nb.py, inline checks).
##   * (c3) part 2 (E(z) = 0), NEW HAND ROUTE replacing the paper's S4 "types I, II have <= 2 lines": p4j.part c3_Qbar shows
##       Qbar = <u_Z,u_Z> = 0 on all of N (Z2 polarised gives <v_j, E(d_Z,z)> = 0, three_iso_perp gives E(d_Z,z) = 0, kerEdb gives
##       d_Z in C z because z_k in {0, tau z}); then Qbar(c) = (1/2)(c2 c3 g23 + c2 c4 g24 + c3 c4 g34) is a NONDEGENERATE quadratic
##       form on the coefficient space C^3 (all g_jk != 0) and cannot vanish on the 2-dim Nbar. Lean: the last step (slicing N by
##       ker col_j + prod_lin + pigeonhole) is still to be written. The underlying plane fact is also decided exactly (COMPUTE r10).
##       DONE in p4k.part (TC5_c3): with Qbar = 0 on N, U = {u_Z} is totally isotropic in V (dim <= 1, iso_image) and the kernel
##       of Z -> u_Z on N lies in the zeta part (v_2, v_3, v_4 independent: indep3), so dim N <= 2 < 3. Branch (c3) COMPLETE.
##   FLp now 14287 lines (R10 = p4c..p4k), Tr10 5261 lines, guard 0, no sorry, no duplicate names.
##   Remaining for TC5: (c1) one line with k = 3 (shares DN_line/DN_on_z; then the S8-type run), (c2-i..iii) lines (v,v,v')
##   ((c2-i) should follow from Fv_nondeg + qbar_pol once the closed forms of DI5.3 (c2) are certified; (c2-iii) needs (F1)/(F2)).
##   Then the TC5 dispatcher: P4_k3 + parallelism case split -> (c1) / (c2) (3 placements via P4_k2_perm-style transport) / TC5_c3.
## RESULT ROUND 9 (leanfl, 23:51- UTC) -- WINDOW 2: FLn.lean COMPILED in 558 s (peak 6.3 GB) with ONLY 12 errors, all in lagcore.part
##   (6 lines, each: `(pow_eq_zero_iff (by norm_num)).mp (by linear_combination ..)` leaves the exponent ?n unassigned because both
##   arguments are postponed tactic blocks). FIX applied in lagcore.part: `pow_eq_zero_iff (n := 2) ...` (certificates re-checked: target
##   a_k^2). So EVERYTHING of rounds 4-7 except LAG_core is Lean-checked: PS (a)-(c), NCOL-P3 (all cases + perm), NCOL-P core, SC1, PR-RED,
##   PR3 complete, Lemma Z (+ polarised), P51 complete, X5 step (1) + X5_mc, TC5 degree conditions (tc5c).  Final theorem
##   PEqualNP.Outside.L_gct_210 still depends only on propext/Classical.choice/Quot.sound.
##   TC5 (P3): classification decided exactly (COMPUTE-leanfl.md round 9; one more chi_1 pair than the paper, same S_4-orbit) and
##   formalized: p3a (generated), p3b, p3c = TC5_P3 (dim Nbar <= 2); p4a TC5_dims ((P4) configuration), p4b S_radical.
## RESULT ROUND 8 (leanfl, 23:10-23:50 UTC; nothing new compiled yet -- window 2 compiles FLn.lean; FLn untouched, md5 19de0ab6...)
##   Written, every linear_combination certificate sympy-checked (leanfl/chk_nb.py, chk_p1.py, chk_p1b.py, chk_chi.py); next-window file
##   lean/fl/FLo.lean = FLn parts + lag nbcore nb p1 p1b p1c p2 nbl nbq (leanfl/build8.sh; 12019 lines, guard/format 0, no duplicate names);
##   small tests: see "Test files" below.
##   (1) LEMMA LAG complete: LAG_a (dim E_zeta >= 2, as: every P inside V orthogonal to E(z0), E(z0,z1), E(z1) has dim <= 1; from
##       LAG_core) and LAG_b (no chi_1-type n is orthogonal to E(z0) and E(z0,z1); Qv coordinates of r1.part).   [lag.part]
##   (2) LEMMA NB complete: B_j isometric (neutral_iso), <z_j, B_j sigma> = 0 (neutral_perp), q = 3 => Nbar = 0 (NB3), S containing a
##       nondegenerate plane => Nbar = 0 (NB_plane); also (C2') qbar_3 = qbar_4 = qbar_5 = 0 (NB_qbar) and qbar_1 = 2 e2(d) (TC5_qbar1).
##   (3) TC5 (P1) COMPLETE (pending compile): TC5_P1 : DefLine K (e_1 - e_2), finrank K >= 5, za, zb independent with za, zb in zeta
##       => False.  Route = verifyfl DI5.3 (P1): P1_nf (z0 in zeta cap V, tau z1 = 1), P1_D (D inside zeta), P1_L (dim L'' >= 3),
##       P1_line (neutral columns on C n, LAG_line), then n non-isotropic: P1_aniso (product-of-linear-forms lemma prod_lin gives
##       y_j = eps_j <s,n> n with eps_j in {0,1}; c = sum eps; c = 1: L'' -> u has isotropic image and kernel <= 1; c != 1: u injective,
##       n = u(Y0) gives (1+c)<n,n>^2 = 0) -- this replaces the paper's four separate c-cases by one computation; n = 0 or all neutral
##       columns zero on L'': P1_van; n isotropic with an active column: P1_iso (<s,n> = 0, u in C n, L'' = n (x) Lam strongly level,
##       A1b on L'' cap ker s gives tau(n^3) = 0), then chi_pow (n_i^4 = -n0 n1 n2 n3 != 0) and LAG_b.
##   (4) TC5 (P2) (p2.part): TC5_P2 : finrank K >= 5 => q <= 2, S contains no nondegenerate plane (all Gram dets of s-values
##       vanish), dim (K cap ker s) >= 3, and every W with zE(W) inside K has dim <= 1 (zeta_le_one, from TC5_P1 via two_indep).
##       Helpers: Z_of_nbar (Nbar-trivial elements are zE(d)), rs_le3, no_nbar.
##   (5) S5 input for (P3)/(P4) (nbl.part): NB_line / NB_lines -- the neutral columns of K cap ker s span a totally isotropic
##       subspace, so each lies on an isotropic line C v_j (tau v_j = <v_j,v_j> = 0); line_of_le_one (dim <= 1 => generator).
##   (6) Nbar equations for (P3)/(P4) (nbq.part): pc_full (permanent = tau/ip/t3 expansion + bracket br, exact), nbar_cubic,
##       nbar_quartic, nbar_eqs: for s(Z) = 0 the u-deletion gives sum_{j!=k} tau(z_j^2 z_k) + tau(z_2 z_3 z_4) = 0 and
##       3 sum_j tau(z_j^2 z_k z_l) - sum_j <z_j,z_k><z_j,z_l> = 0 (verifyfl (P3) formulas; leanfl/chk_nbar.py, exact).
##   Test files: leanfl/Tr8full.lean = closure of all R8 parts (2916 lines; leanfl/closure.py picks only the 117 FLn blocks they
##   need; R8 = lag nbcore nb p1 p1b p1c p2 nbl nbq) -- listed as optional 2nd entry in window_files.txt after FLn; leanfl/Tr8.lean (1716 lines, generic parts only) as fallback.
##   Not done: rest of X5 step (2) (only the exact Groebner part is left; no hand statement); TC5 (P3), (P4): (P3) needs the
##   classification of isotropic pairs with tau(v v'^2) = tau(v^2 v') = 0 WITHOUT the bracket condition (the Lean HypIIa has br = 0
##   as an extra hypothesis), (P4) is the long branch list (N-a), (N-b), (c1)-(c3).
## RESULT ROUND 7 (leanfl, ~22:57-23:10 UTC; + LAG_core (heart of Lemma LAG (a)); nothing new compiled yet -- window 2 compiles FLn.lean, ~02:00-02:30 UTC)
##   FLn.lean = FLm (byte-identical prefix) + x5b + tc5c + x5c (10523 lines, 487 KB, guard/format 0; window_files.txt -> FLn).
##   X5 hand part (rows R7.3): step (1) rank1_col (r6) + X5_struct (B_a v = B_b v = v) + X5_perp (B_b = -B_a on v^perp, B_a keeps
##   v^perp); step (2) first conclusion X5_mc: m_c = 0 in every (5,1) space with such a kernel -- by a SHORTER argument than rows'
##   (no case split on m_a, m_b, no VF-A/TC5; flagged for verify2). TC5 groundwork: TC5_degree (DI5.2 (C1')-(C4'), raw form).
##   Not done: rest of X5 step (2) (normal form of N for the exact computation), LAG (Groebner certificate infeasible: saturation
##   proves LAG(a) is consistent but a0^k in I needs k > 6), NB, TC5 (P1)-(P4), NCOL2-P.
## RESULT ROUND 6 (leanfl, 22:32-22:50 UTC; nothing new compiled yet -- window 2 compiles FLm.lean ~01:00-02:00 UTC)
##   FLm.lean = FLl + lz lzp p51a p51b p51c p51d (10076 lines, 467 KB, guard/format 0; leanfl/build.sh; leanfl/window_files.txt).
##   Written, every certificate sympy-checked: verifyfl LEMMA Z ((Z1) eps(D,zeta) = 0 and all of (Z2), also polarised in z, z';
##   lz/lzp) and rows' THEOREM P51 complete: P51_i (distinct entries, principal H closed under single columns: types (1,1,1), (2,1),
##   (3) => finrank K <= 4), P51_ii_core (two-column H, m_a != m_b, dim N >= 2 => full free column), P51_two / P51_two_perm
##   (any two-column H => finrank K <= 4). Proof route of P51 (i) streamlined: rank-one law Z = a m^T, derivative at column 4
##   gives <x,E_2(a)> = <x,E_3(a)> = 0 directly (no case m_n = 0), then E_2, E_3 constant => pairwise products of a vanish
##   (radical certificate (a0 a1)^2 in (e2(a_{-i}))), then a 2-line dimension lemma.  Not done: NCOL2-P, X5/PR5 wrappers, TC5.
## RESULT ROUND 5 (leanfl, 21:07- UTC). WINDOW 1 (22:20): FLk.lean = guard-compliant FL strand (final theorem PEqualNP.Outside.L_gct_210)
## COMPILED on this machine, exit 0, axioms propext/Classical.choice/Quot.sound, peak 6.2 GB. Tps2 (all new core parts not needing r1):
## only 2 errors, both a binder-type slip in NCOL_P_core (fixed); so PS (a)-(c), NCOL-P3 (all cases), sq_prop, PR-RED core, PR3 step 1,
## PS_bil and the SC1 polar formula are Lean-checked modulo that fix. Untested until window 2: SC1 (sc1b), PR3 steps 2-4, wrappers.
##   Written and sympy-checked on top of round 4 (all in FLl.lean = leanfl/build.sh; 9096 lines, 421 KB, guard/format 0):
##   SC1 (rows R5.6; sc1a/sc1b), PR-RED (verifyfl R4.4; prred), THEOREM PR3 (verifyfl R4.5; pr3a-pr3e: step 1 Z_* = v l^T with
##   tau(v^3) = 0, step 2 Qv normal form of Z, cubic at the neutral column, Lagrange-identity finish), PS_bil (polar of PS (b); ps6).
##   Deviation in PR3: instead of "rank 3 quadratic form vanishing on a plane" the proof varies b in Z1 + b Zs: Q(l) = 0, B(p,l) = 0,
##   then det Q(p)^2 lies in the ideal (Q(l), B(p,l)) (explicit certificate) and det = -<m,m>/2 != 0 forces Q(p) = 0, so e3 = 0.
##   T3 / Lemma O3: assessed, not formalized (needs SO(3,C) = PSL_2(C)); see handover section 7.
## RESULT ROUND 4 (leanfl, local machine, 19:40-20:50 UTC) -- read this first; the round 1-3 RESULT below is unchanged and still valid.
## (1) GUARD: FL.lean (= v32 = FLj, compiled in the cloud) is refused by the PROJECT guard only because its last theorem is named
##     PEqualNP.Outside.L_gct_210_fl. FIXED in w.tail (name PEqualNP.Outside.L_gct_210, statement SL /\ FL row /\ FL col unchanged);
##     FLk.lean = v32 parts + w.tail passes outside-guard.mjs and the leancheck guard/format counts (all 0). Namespaces and add_ lines
##     were already compliant since v25. Local compile of FLk: NOT YET FINISHED (two runs killed at 25 min by machine memory starvation,
##     peak 0.84 GB, Lean never finished importing Mathlib; re-queued with the new 60-min limit).
## (2) NEW PARTS, WRITTEN, ALL linear_combination CERTIFICATES SYMPY-CHECKED, BUT NOT YET COMPILED (no Lean run could complete):
##     ps.part    verifyfl THEOREM PS (a) normal form (PS_nf) + rows THEOREM NCOL-P3 three-column core (NCOL_P3_core);
##     ps4.part   sq_prop, PS_b_core (PS (b): <f,f> = 3 kappa^2/4 in the normalisation z_j = (kappa m_j/4) 1 + m_j phi_j(Y_f));
##     ps5.part   PS_c_core (PS (c): principal stratum => finrank K <= 5);
##     np3b.part  NCOL-P3 two-column (m_a m_b = 0, by pairing (m_a - m_b) g_a + (m_a + m_b) f = 0 with itself) and one-column cores;
##     ncolp.part rows THEOREM NCOL-P (R5.7) steps (2)-(4) (NCOL_P_core: K principal with V spanned by single-column elements of H
##                => some column carrying a single-column element is neutral); step (1) (K strongly level) enters as the hypothesis SLev H;
##     ps2.part / ps3.part / np3c.part: DefLine wrappers ThmPS_a/b/c, NCOL_P3, NCOL_P3_two, NCOL_P3_one, NCOL_P; column-permutation
##                versions NCOL_P3_perm, NCOL_P3_two_perm.
##     Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1
##            ps ps4 ps5 np3b ncolp ps2 ps3 np3c (.part) w.tail > FLl.lean   (8287 lines, 381 KB; guard and format 0).
##     Quick test of all new proofs except the wrappers: leanfl/Tps2.lean (pre a b c + colsumL snippet + ps ps4 ps5 np3b ncolp).

## RESULT (leanfl, rounds 1-3) -- Lean-checked WITHOUT ANY HYPOTHESIS: LEMMA SL, THEOREM FL (row and column), LEMMA DS, the DEFECT
## CONSTRUCTION (Prop. D / normal form R1), LEMMA EQ, THEOREM SPLIT (both forms), THEOREM FS, LEMMA HYP, the HYPERPLANE LEMMA, LEMMA SL_3,
## THEOREM NCOL-S (a), (b), the TC5 NORMAL FORM (DI5.2) and LEMMA Z (Z1, first part), LEMMA QB, R4.2 (a), (b), (c), R4.15 (F1), (F2), and the
## NEW 4x5 analogue FL45 of Theorem FL (level 4x5 space with a full free row has dim <= 6).
## Not done: TC5 itself (DI5.3), TS, PS, PR3, FL2*, R4.2 (d), R4.3.
File: /home/claude/work/L-gct-210/lean/fl/FL.lean (the last STATUS line names the current snapshot FL.vNN.lean, its size and the build list).
leancheck: exit 0; axioms propext / Classical.choice / Quot.sound only; format counts all 0; GUARD counts 0/0 (helpers live in
namespace PEqualNP.Outside.L_gct_210_aux.FL, no line begins with add_; adopted in v25). Size is above 300 KB (cap waived by the coordinator).
Final (placeholder-named) theorem, no hypotheses, last declaration of the file:
  theorem PEqualNP.Outside.L_gct_210_fl :
      (forall K : Submodule C (Fin 4 x Fin 5 -> C), SLev K -> finrank K <= 3)                                   [LEMMA SL]
    /\ (forall L, <gap hypothesis verbatim> -> forall r, (forall w, sum w = 0 -> e_r w^T in L) -> finrank L <= 7)      [THEOREM FL, free row]
    /\ (forall L, <gap hypothesis verbatim> -> forall c, (forall w, sum w = 0 -> w e_c^T in L) -> finrank L <= 7)      [THEOREM FL, free column]
All other results are theorems of the namespace PEqualNP.Outside.L_gct_210_aux.FL in the same file. NO formalized step failed and NO
error was found in any of the paper proofs that were formalized (blueprint S1-S9, chief's DS, rows' D / R3.8 / R4.1 / R4.14 / R4.2(a,b),
rows' R4.2(c) / R4.15(F1,F2), verifyfl's DI5.1 / DI5.2 / R3.1 / R3.2 / R3.3 / R4.1(QB)).

### Main theorems (Lean names; all COMPILED, no hypotheses)
| paper statement | Lean name (helpers) | statement in Lean terms |
| Lemma SL (strongly level 4x5 => dim <= 3) | LemmaSL | SLev K -> finrank K <= 3 |
| Theorem FL, full free row | TheoremFL_row | level L, rowMat r w in L for all sum-zero w -> finrank L <= 7 |
| Theorem FL, full free column (transposition) | TheoremFL_col (gap_swap5, trE5, FL_col_of) | same with colMat c w |
| Corollary (stage A + SL) | Cor_row, Cor_row7 | SLev ((L inf ker (rowP r)).map (del r)) -> finrank L <= finrank (L.map (rowP r)) + 3; <= 7 if all row-r sums vanish |
| chief's Lemma DS | LemmaDS (P4_poly, P4_ones, DS_star, DS_i) | level L, row r deletable -> all row-r sums vanish; if finrank (L.map (rowP r)) = 4 then L cap {row r = 0} is strongly level and finrank L <= 7 |
| rows' Prop. D (a): defect construction | defL, defL_level, defL_deletable, defL_finrank, defL_finrank' | Lev45 K -> defL r K = K (+) e_r (x) defW K is a 5x5 level space with row r deletable, finrank = finrank K + finrank (defW K) |
| rows' Prop. D (b) / normal form R1 | defect_conv, defect_conv' | ANY level L: finrank L <= finrank L' + finrank (defW L'), L' = L.map (del r); finrank L + finrank (defC L') <= finrank L' + 5 |
| dim W = 4 - e | defW_finrank (dotL, dotL_ker) | finrank (defW K) + finrank (defC K) = 5, defC K = span{C(Y)} = C(L') + C 1 (finrank defC = e + 1) |
| strongly level = defect 0 | defW_SLev, defW_le, defW_sum | SLev K -> defW K = sumZero 5; always defW K <= sumZero 5 |
| verifyfl's Lemma EQ (DI5.1) | LemmaEQ, LemmaEQ_cols | DefLine K m, column permutation pi with m (pi j) != m j -> K cap Fix(pi) strongly level, finrank <= 3; m a != m b -> K cap {col a = col b} strongly level and finrank K <= 3 + rank(Y -> y_a - y_b) |
| verifyfl's THEOREM SPLIT (R3.1) | ThmSplit (repl, P4_repl_add, per_stk, per_rows, P4_sym) | DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K -> K cap {<m, row i> = 0} strongly level and finrank K <= 4 |
| SPLIT, ker kappa form (step (3) of R3.1) | ThmSplit_kappa (split_id, split_ker, pc_ev, P4_repl_ones, P4_lin) | same hypotheses -> K cap {all column sums 0} strongly level, finrank <= 3 |
| verifyfl's THEOREM FS (R3.2), row form | ThmFS (rowL, fsMap) | defect space Cs inside 1^perp, e_i (x) Cs inside K, <,> nondegenerate on Cs -> K cap {row i perp Cs} strongly level, finrank K <= 3 + finrank Cs |
| verifyfl's Lemma HYP (R3.3) (a), (b) | LemmaHYP_a, LemmaHYP_b (hyp4, colsumL) | (a) H <= K, DefLine K m, finrank H = 4 -> DefLine H m and H not strongly level; (b) if every 4-dim space with defect line C m contains some e_i m^T then no 5-dim space with defect line C m exists |
| rows' Hyperplane Lemma (R4.1) | HyperplaneLemma, HyperplaneCor | (DI_5; e-1) as "finrank (defC K) <= e -> finrank K <= finrank (defC K) + 2"; L' level, finrank (defC L') = e + 1, K <= L' -> defC K = defC L' or finrank K <= finrank (defC K) + 2; if finrank K >= e + 3 then defC K = defC L' |
| rows' Lemma SL_3 (R3.8), zero-row form | LemmaSL3 (Vp_span, Vp_nondeg, Vp_t3, Vp_finrank, SL3_q2, SL3_two, SL3_d2) | SLev K and row i of every Y in K is zero -> finrank K <= 2 |
| rows' Theorem NCOL-S (a) (R4.14) | NCOL_S_a (kc1, P4_poly1, kc1_eq, pc_ev2, P4_repl2, kc1_formula, split_eig, ncol_lin, tau_repl0) | DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K, m without zero entry -> row i vanishes on N = K cap {<m, row i> = 0} and finrank K <= 3 |
| rows' Theorem NCOL-S (b) | ncol_core, ncol_b1, NCOL_S_b (P4_zero_row') | for all Y in K the column sums of the rows != i are equal on supp m; if n is the only zero of m: row i of N is supported at n, N cap {row i = 0} strongly level of finrank <= 2, = 2 if finrank K = 4 |
| verifyfl's TC5 normal form (DI5.2) | uY, dY, e2, Ed, TC5_sum, TC5_diff, TC5_n2, TC5_n3, TC5_n4, TC5_dd, TC5_normal | the four displayed identities; DefLine K (e_0 - e_1) <=> for all Y in K: (i) [u,y_2,y_3,y_4] level and (ii) perm(J+[u,u,y_k,y_l]) - perm[d,d,1+y_k,1+y_l] = 24 (columns numbered 0..4) |
| verifyfl's Lemma QB (R4.1) | LemmaQB (qA1, qA2, P4_quad, qb_lin, qA1_eq, qA2_eq) | DefLine K m, sum m = 0, m != 0, Y in K -> exists kappa theta2: column sums = kappa m; (a) sum_a <y_a,y_a> = <s,s> + kappa^2 <m,m>; (b) <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(theta2/2) m_j |
| QB (a) for any level 4x5 space; R4.2 (a), (b) | Lev45_quad, single_row_sum, single_row_perp, single_row_defC (rowE) | Lev45 K, Y in K -> total sum 0 and sum_a <y_a,y_a> = <s,s> + sum_a c_a^2; e_i u^T in K -> sum u = 0 and u in defC K; e_i u^T, e_k u'^T in K, i != k -> <u,u'> = 0 |

| rows' R4.2 (c) | single_row_t3 | Lev45 K, three distinct rows i, k, l with e_i u^T, e_k u'^T, e_l u''^T in K -> sum_j u_j u'_j u''_j = 0 |
| NEW: Theorem FL for 4x5 level spaces | FL45 (zrow, one_add_zrow, FL45_core) | Lev45 K and e_i w^T in K for all sum-zero w -> finrank K <= 6. Core: for Y in K the matrix 1 + Y with row i replaced by ones has all five P4 equal and (5 + row-i sum) * P4_0 = 120, so the image of K under zrow i (zero out row i) is strongly level with a zero row, finrank <= 2 by LemmaSL3; the kernel is F_i, finrank 4 |
| rows' R4.15 (F1), (F2) | Di_mem, R415_F1, R415_F2 | Lev45 K, e_i u^T in K, Y in K: D_i(Y)u = (P4 b (repl i u (1 + Y)))_b lies in defC K and has sum 0; (F1) the vector (tau(column b of Y without row i) * u_b)_b lies in defC K and sums to 0; (F2) e_k u'^T in K, k != i -> (u'_b u_b)_b in defC K |
| glue between the three level notions | SLev_Lev45, DefLine_Lev45, SLev_DefLine | SLev K -> Lev45 K; DefLine K m and sum m = 0 -> Lev45 K; SLev K -> DefLine K m for every m |
| NCOL-S corollary (a neutral column exists) | NCOL_S_neutral | hypotheses of SPLIT and 4 <= finrank K -> exists n, m n = 0 |
| verifyfl's Lemma Z (Z1), first part | LemmaZ1 (zE, pc_ones) | DefLine K (e_0 - e_1) and z(e_0 - e_1)^T in K -> e2 z = 0, e2 z = (tau(z)^2 - <z,z>)/2 (Q = 0 on zeta) |
### Dictionary / API guide
  M55 = Fin 5 x Fin 5 -> C, M45 = Fin 4 x Fin 5 -> C, V4 = Fin 4 -> C.  col Y j (column), rs Y (row sums, linear), tau, ip, t3, t4, br.
  P4 a N        = permanent of the 4x4 matrix "N minus column a" (sum over injective e : Fin 4 -> Fin 5 avoiding a); C(Y)_a = P4 a (1 + Y).
                  P4_cols: P4 a N = pc (col N (a.succAbove 0)) .. (col N (a.succAbove 3)); pc = 4x4 permanent in column form; sa0..sa4
                  turn a.succAbove k into literals; P4_c0..P4_c4 are the literal versions; pc_tau, pc_expand expand pc.
  SLev K        = forall Y in K, forall a, P4 a (1 + Y) = 24            (strongly level = defect 0).
  Lev45 K       = forall Y in K, sum_a P4 a (1 + Y) = 120              (4x5 level: <1, C(Y)> = 120).
  DefLine K m   = forall Y in K, exists theta, forall a, P4 a (1 + Y) = 24 + theta * m a     (defect line C m; sum m = 0, m != 0 are separate hypotheses).
  defW K        = {w : forall Y in K, sum_a w a * P4 a (1 + Y) = 0} = (C(K) + C 1)^perp  (mem_defW is Iff.rfl).
  defC K        = span{C(Y) : Y in K} = C(K) + C 1;   defect e(K) = finrank (defC K) - 1.
  defL r K      = K.comap (del r) inf (defW K).comap (rowP r)      (the space L(L') of rows' Prop. D).
  "row r deletable in L"  :=  forall t in L, sum_a P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120.
  rowMat r w = e_r w^T (5x5), colMat c w, rowE i u = e_i u^T (4x5; the hypotheses "e_i m^T in K" are written with the same lambda),
  del r = delete row r, rowP r = row r, ins r Y = Y with a zero row inserted at r, stk r N w = (N; w), cperm sigma = column permutation.
  repl i u N    = N with row i replaced by u (repl_at, repl_ne, repl_self).  P4_repl_add (additivity in a row), P4_zero_row, P4_zero_row',
                  P4_sym r i w u N: sum_a w a * P4 a (repl i u N) = sum_a u a * P4 a (repl i w N)  (symmetry of Per(l_1..l_4, w)).
  Polynomial tools: P4_poly a B Y (P4 a (B + sY) has degree <= 4 in s), P4_poly1 (same with the constant and linear coefficients explicit:
                  P4 a B and kc1 a B Y = sum_k P4 a (repl k (row k of Y) B), kc1_eq), P4_lin, P4_quad (P4 b (1 + cY) with explicit
                  coefficients qA1, qA2 of c, c^2; closed forms qA1_eq, qA2_eq), roots5 (degree <= 4, five distinct roots => all
                  coefficients 0; used with the nodes 1..5 = inj_succ5), moments5 (Vandermonde, transposed), vdm3, cramer2.
  Explicit permanents: P4_ones (= 24), P4_repl_ones (row i = m, others 1: 6 sum_{j != b} m_j), P4_repl2 (rows y, m, 1, 1: 2 sum_{j != l} y_j m_l).
  phiRow i m Y  = <m, row i of Y>;  colsumL j Y = column sum j;  csL = all column sums;  fsMap i Cs : M45 -> Dual Cs.
  Plane V' = {x in C^4 : tau x = 0, x_i = 0} (zero-row case): Vp_span (two independent vectors span it), Vp_nondeg, Vp_t3, Vp_finrank.
  SL_3 dictionary: a 3x5 space "all of whose 3x4 column deletions are level" corresponds to the 4x5 space of its zero-row extensions
  (Laplace expansion of P4 a (1 + Y) along the all-ones row i); this Laplace step itself is not formalized.
  How to add a result: write a new part file, append it before v.tail in the build list, compile with leancheck (5 min for the whole
  file); never start a line with add_; brute-force identities about pc: simp (config := {decide := true}) only [pc, ..., Fin.sum_univ_four,
  ite_true, ite_false, add_zero, zero_add] then ring (at most ~4 such cases per declaration, else the heartbeat limit is hit);
  avoid `exact` across non-syntactic pc arguments (whnf timeout): first rewrite the columns with a `have hc : forall j, col .. j = .. := fun j => rfl`.

### Blueprint steps S1-S9 (rounds 1-2): all COMPILED, no hypothesis
  S1 Prop R (perm5_row, level_row, propR, stageA); S2 Lemma C (pc_tau, pc_expand, coeffs, C1, C2, C34, C2pol); S3 (Q1, Q4, Niso, peel, maxpt, tricho);
  S4 Lemma A incl. G23 (A1, A1b, A1cols, G23, pattern23, LemA2_proof, caseA3, LemA_proof, two_line_pattern); S5 (Bi, Bii, Biii);
  S6 type IV excluded (HypS6_proof: spv/chart, Uv, lamL, N_coords, star_cert, Lam_star, Lam_F, singA, pairB, core5, AlgCore_of, HypS6_of,
     caseC_alg, HypS6C_proof); S7 type II excluded (typeII_ids, IIa_tu, Ps4*, HypIIa_proof, S7_elem, S7_step, HypS7alg_of, HypS7_of);
  S8 type I excluded (S8_elem, S8_step1, Qv framework, S8a, S8b, HypS8_proof); S9 (No22, SL_of, FL_of).

### Deviations from the paper proofs in rounds 2-3 (all simplifications or re-arrangements; none is a gap in the paper)
 - S8 Steps 2-4 and S6 are done WITHOUT any row permutation: coordinates Qv v a0 a1 a2 a3 = a0 + a1 v + a2 v^2 + a3 v^3 for a "special"
   vector v (tau v = <v,v> = tau(v^3) = 0, v_i^4 = kappa): products are a twisted convolution (Qv_mul), tau and <,> are read off (tau_Qv, ip_Qv).
 - S6 chart: the six special lines are spv pi (pi in Perm(Fin 3)), 6 > 5 columns (pigeonhole), so some special v is proportional to no column
   of the generic element z; then every column is zeta_m U(theta_m), U(theta) = Qv v 0 (-theta^2/2) theta 1 (no "point at infinity").
 - S6 (C3*): one polynomial certificate (star_cert); division by lam_m via the parallelogram law with the generic element (Lam_F).
 - S6 patterns: singleton lines by singA; (2,1,1,1) by pairB; (1^5) by caseC_alg: with w in Lam having four vanishing moments and theta w
   in Lam, the power sums p_j = sum w_n^2 theta_n^j satisfy p_0 = ... = p_4 = 0, hence w = 0 by Vandermonde (replaces the case distinction
   c_0 = 0 / c_0 != 0 and the explicit partial fractions of the blueprint).
 - Lemma DS (i): the limit s -> 0 is replaced by "a polynomial of degree <= 4 vanishing at s = 1..5 vanishes identically" (P4_poly, roots5);
   the same device is used for every "degree-k part" (SPLIT step (3), NCOL-S, QB).
 - Prop. D (b) is proved for every level L (the inequality does not use deletability).
 - THEOREM SPLIT: steps (1), (2) of R3.1 give directly "K cap {<m, row i> = 0} is strongly level" (the form used by rows' R4.14);
   step (3) is the separate lemma split_ker (column sums 0 => <m, row i> = 0).  THEOREM FS is proved in the same row form.
 - LEMMA SL_3, case (q, d) = (1, 2): NEW SHORT ARGUMENT replacing R3.8 (d). With N = span{v(e_a-e_b)^T, w(e_c-e_d)^T}, Y_0 in K, u = s(Y_0):
   C3 at the inactive column e, second difference in the direction w(e_c-e_d)^T: tau(y_a w^2) + tau(y_b w^2) = 0; on the plane V' this is
   gamma_w (<y_a,v> + <y_b,v>) = 0; C2pol with v(e_a-e_b)^T at columns a, b: 2<y_a,v> = <u,v> = 2<y_b,v>; so <u,v> = 0, likewise
   <u,w> = 0, and u = 0 because <,> is nondegenerate on V' = span(v,w). Hence d = 2 forces q = 0 (SL3_d2); q = 2 forces N = 0 (SL3_q2).
 - NCOL-S: D^(1)(Y) m is used in the raw form 2 sum_{j != b} c_j sum_{l != b,j} m_l (kc1_formula) and then in the closed form
   -2 S m_b + 4 c_b m_b - 2 c.m (ncol_core); c.m = 0 is obtained in one stroke by summing the eigenvector relations over b (no case
   distinction "m has a zero / has no zero"), so ncol_b1 holds for every m with <m,m> != 0.
 - QB is stated before centring ((b) as <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(theta2/2) m_j, theta2 = the degree-2 part of thetahat);
   Lev45_quad is the general-e statement (a) with <c,c> = sum of squared column sums.
 - TC5_dd holds for arbitrary a, b (the hypothesis a, b in V of DI5.2 is not needed for that identity).

### Open (not formalized)
 - verifyfl's Theorem TC5 (DI5.3: Lemma Z beyond the first part of (Z1), Lemmas LAG, NB, branches P1-P4 incl. the simplified (c3)),
   Theorem TS, Theorem PS / PR-RED / PR3 (R4.3-R4.5), round-5 items; rows' FL2* (R3.9), R4.2 (d), R4.3, R4.15 beyond (F1), (F2);
   the degree-wise conditions (C2'), (C3'), (C4') of DI5.2; the native 3x5 statement of SL_3.
   Tools that are ready for them: everything in the API guide; for PS the blueprint lemmas ip_phi / tau_phi / Biii (B_j isometries) and
   LemmaQB; for FL2* the pieces P4_repl2, kc1_formula (= Delta_1 u), LemmaSL3, single_row_perp, single_row_t3, FL45, Di_mem, R415_F1/F2;
   for TC5 the normal form TC5_normal with TC5_dd and LemmaZ1 (pattern: evaluate the normal form on z(e_0-e_1)^T and on Y + t z(e_0-e_1)^T).

### Build recipe (reproduces FL.lean byte for byte; leancheck takes about 5 minutes for the whole file)
  cd lean/fl; cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1 (.part) v.tail > FL.lean
  (rounds 1-2: pre .. n blueprint S1-S9; r1 Qv; r2 S8; s1-s3 S6; t3 SL / FL row + column / corollaries; ds Lemma DS;
   round 3: x1 Prop. D + Lemma EQ; x2 SPLIT; x3 defect dimension + R4.1 + HYP; y1 SL_3; x4 SPLIT ker kappa; n1 NCOL-S (a); n2 NCOL-S (b);
   z1 FS; z2 TC5 normal form; q1 QB; r4 Lev45_quad + R4.2 (a), (b); r5 R4.2 (c); f1 FL45; g1 R4.15 (F1), (F2); h1 glue lemmas,
   NCOL_S_neutral, Lemma Z1; v.tail final theorem.)
  Snapshots (all compile): FL.v14 (round 1), v15 (S8), v16 (column), v17 (S6 mod (1^5)), v18 (hypothesis-free FL), v19 (DS), v20 (D, EQ, SPLIT),
  v21 (defect dim, R4.1, HYP), v22 (SL_3), v23 (SPLIT kappa), v24 (NCOL-S a), v25 (NCOL-S b, GUARD-COMPLIANT from here on), v26 (FS, DI5.2),
  v27 (QB), v28 (Lev45_quad, R4.2 a, b), v29 (R4.2 c), v30 (FL45), v31 (R4.15 F1, F2), v32 (glue, NCOL_S_neutral, Lemma Z1) = FL.lean.  Files *.bak_v24 are the pre-guard versions of the five edited parts.

## RESULT ROUND 1 (superseded by the section above; kept for the per-step table and the round-1 deviations)
## THEOREM FL was Lean-checked modulo TWO explicit hypotheses: HypS6 (blueprint S6, type IV) and HypS8 (S8 Steps 2-4, type I).
File: /home/claude/work/L-gct-210/lean/fl/FL.lean (3091 lines, 136 KB; identical snapshot FL.v14.lean). leancheck: exit 0, axioms
propext / Classical.choice / Quot.sound only, format counts all 0 (no sorry, no comments, no banned words, no quotes, no hash).
Final theorem (helpers in namespace PEqualNP.Gct.FL210):
  theorem PEqualNP.Outside.L_gct_210_fl (H6 : HypS6) (H8 : HypS8)
      (L : Submodule C (Fin 5 x Fin 5 -> C)) (hL : <gap hypothesis verbatim>) (r : Fin 5)
      (hF : forall w : Fin 5 -> C, sum w = 0 -> (fun p => if p.1 = r then w p.2 else 0) in L) : finrank C L <= 7
Lean-checked without any hypothesis: S1 (Prop R), S2 (Lemma C), S3, S4 (LEMMA A: d <= 2, complete, incl. G23), S5 (B-i, B-ii, B-iii),
S7 (TYPE II EXCLUDED, complete, incl. (II-a) and (II-b)), S9 and Stage C modulo the two hypotheses.
NO formalized step failed, and no error was found in the paper proof in the formalized part; the only deviations are simplifications.
NOT Lean-checked (both true according to the blueprint; exact statements below):
  HypS6 : three linearly independent column lines cannot occur with d = 2            (S6: type IV does not exist)
  HypS8 : a rank-one-column N = v (x) Lambda with d = 2 cannot occur when q = 2      (S8: type I; Step 1 is proved, Steps 2-4 open)

### Status per blueprint step
| step | Lean names | status |
| S1 ID1 Laplace expansion of perm_5 along row r | perm5_row (sum_emb_perm, sum_emb_succ, emb4) | COMPILED |
| S1 Prop R (row-r sum 0; all five column deletions level; L = F_r (+) L') | level_row, propR, stageA | COMPILED |
| S2 ID2 perm(J_4 + cZ), general columns, all four coefficients | pc_tau, pc_expand, coeffs, coeffs0, P4_eq, P4_c0..4, P4_cols | COMPILED |
| S2 Lemma C (C1, C2, C3, C4) and (C2pol) | C1, C2, C34, C2pol, sl_cols | COMPILED |
| S3 (Q1) totally isotropic subspace of V has dim <= 1; (Q4) | Q1, Q4 (perp_bound, finrank_sup_one, perp_sup_one, nondeg) | COMPILED |
| S3 Lemma N: columns of N mutually isotropic, column spaces of dim <= 1 | N_iso, N_col_dim, Niso, Ncol1 | COMPILED |
| S3 structure "forms l_m, K, g" | maxpt (generic element z of N whose columns span all column lines), tricho | COMPILED (replaces l_m, K) |
| S4 (P-a)/(P-b): isotropic v with tau(v^3) = tau(v^4) = 0 is 0; v_i^4 = tau(v^4)/4 if tau(v^3) = 0 | root4, iso34, root4k, pow4_iso | COMPILED |
| S4 (A1) g = 1: dim N <= 2; tau(v^3) != 0 => dim <= 1; tau(v^4) != 0 => two inactive columns | A1facts, A1, A1b, A1cols (generic_t, generic_pt) | COMPILED |
| S4 (G23) the (2,3) pattern does not exist (verifyfl's repaired version) | br_w3, G23core, G23, pattern23 | COMPILED |
| S4 (A2) g = 2: dim <= 2 and only the (2,2) pattern occurs | LemA2_proof, two_line_pattern | COMPILED |
| S4 (A3) g >= 3: dim <= 2 | caseA3 (peel, perm_two/three/four) | COMPILED |
| S4 LEMMA A: d <= 2 | LemA_red, LemA_proof | COMPILED, no hypothesis |
| S4 classification of d = 2 | tricho + two_line_pattern + A1b + A1cols (inside No22) | COMPILED in the form needed |
| S5 (B1)-(B3) | ip_phi, tau_phi, ip_col_phi, sum_phi | COMPILED |
| S5 (B-i) q = 3 => N = 0 | Bi | COMPILED |
| S5 (B-ii) q = 2, N != 0 => exists u in S, u != 0, u perp S | Bii | COMPILED |
| S5 (B-iii) b_m in C v_m | Biii | COMPILED |
| S6 preliminary: with d = 2 and three independent column lines all five columns are active | S6_active (cols_zero) | COMPILED |
| S6 type IV does not exist | HypS6 | SKETCHED: hypothesis H6 of the final theorem |
| S7 on N: tau(v w^2) = tau(v^2 w) = 0, [v,v,w,w] = 0 | typeII_ids | COMPILED |
| S7 ID7: E(t,u) -+ E(u,t) factorisations, bracket at a = 0, b^2 = 4, a^2 b = -8 | IIa_tu | COMPILED |
| S7 (II-a): v o v in C w and w o w in C v (incl. the point at infinity, S11) | Ps4, Ps4_mul, Ps4_param, ip_Ps4, IIa_pqr, sq_Ps4, HypIIa_proof | COMPILED |
| S7 (II-b): <u, w^2> = <u, v^2> = 0 from C3 at the inactive column (raw equation; verifyfl's "reader's trap (b)") | S7_elem, S7_step | COMPILED |
| S7 (II-b) conclusion: type II impossible for q = 2 | HypS7alg_of, HypS7_of | COMPILED, no hypothesis |
| S8 explicit elements v (e_a - e_b)^T of N; Step 1: <v^2,u> = <v^2,b_4> = <v^2,b_5> = 0 | col_outer, S8_elem, S8_step1 | COMPILED |
| S8 Steps 2, 3, 4 (type I excluded) | HypS8 | SKETCHED: hypothesis H8 of the final theorem |
| S9 (2,2) impossible; Lemma SL | No22, SL_of | COMPILED (from H6, H8) |
| S9 / Stage C: Theorem FL | FL_of, PEqualNP.Outside.L_gct_210_fl | COMPILED (from Lemma SL) |
FAILED: none.

### Definitions used in the statements
  M55 = Fin 5 x Fin 5 -> C, M45 = Fin 4 x Fin 5 -> C, V4 = Fin 4 -> C.
  P4 a N   = sum over injective e : Fin 4 -> Fin 5 with e k != a for all k of N(0,e 0) N(1,e 1) N(2,e 2) N(3,e 3)
             (= permanent of "N with column a deleted"; perm5_row ties it to the 5x5 permanent, P4_cols to the column form).
  SLev K   = forall Y in K, forall a, P4 a (1 + Y) = 24                                   (strongly level)
  del r    = delete row r (5x5 -> 4x5 via Fin.succAbove), rowP r = row r, rowMat r w = e_r w^T.
  tau, ip, t3, t4, br : explicit 4-term sums for tau(x), <x,y>, tau(xyz), tau(xyzw), and the bracket; col Y m; rs = row-sum map.
  phi m = 2 col_m - rs  (B_m of the blueprint, defined on all of K: no section sigma -> Y(sigma) needed).
  indep v w = (s v + t w = 0 => s = t = 0);  outer v x = v x^T;  cperm sigma = column permutation (SLev_perm: SLev is invariant).
  Ps4 j a0 a1 a2 a3 = a0 chi_0 + a1 chi_1 + a2 chi_2 + a3 chi_3 with j in the role of i (only j*j = -1 is used).
  stageA: SLev (L.map (del r)), SLev ((L inf ker (rowP r)).map (del r)), finrank L <= 4 + finrank ((L inf ker (rowP r)).map (del r)).

### The two open hypotheses (exact Lean: `def HypS6`, `def HypS8` in FL.lean)
  N := K inf ker rs.  "z spanning" := z in N and every column of every Z in N is a multiple of the same column of z (exists: maxpt).
  HypS6 : N strongly level, rs = 0 on N, finrank N = 2, z spanning, three columns a, b, c of z linearly independent, and ALL FIVE
          columns of z nonzero (proved: S6_active)  =>  False.
          (S6; uses N only. Covers type IV = patterns (2,1,1,1), (1^5); the patterns (3,1,1), (2,2,1) are also inside this
           hypothesis -- they are vacuous by the singleton-line argument of S3, which is NOT formalized separately.)
  HypS8 : K strongly level, finrank (K.map rs) = 2, finrank N = 2, Yu in K with u := rs Yu != 0 and u perp S, N inside v (x) C^5 with
          v != 0, tau v = 0, <v,v> = 0, tau(v^3) = 0, sigma a column permutation such that the columns sigma 3, sigma 4 vanish on N,
          and (Step 1, proved) tau(v^2 u) = 0, tau(v^2 b) = 0 for b = phi (sigma 3) Yu and b = phi (sigma 4) Yu  =>  False.
          (S8 Steps 2-4. b_m = phi m Yu is the blueprint's B_m u; for the active columns sigma 0..2 one has b_m in C v by Biii,
           using the elements of N produced by S8_elem.)
  Tools ready for both: Biii (b_m in C v_m), ip_phi / ip_col_phi / sum_phi, C34 and C2pol on K, SLev_perm + sa0..sa4 to put columns in
  standard position (patterns: pattern23, typeII_ids, S7_step), S7_elem (explicit elements of N from finrank N = 2 via `peel`),
  S7_step (coefficient extraction by three evaluations Yu + W, Yu - W, Yu), pow4_iso (v_i^4 = tau(v^4)/4), Q1/Q4, generic_pt,
  and the group-algebra coordinates: Ps4_param (every x in V is Ps4 j 0 p q r), Ps4_mul (entrywise product = convolution on Z/4, so
  all tau(products) become j-free polynomials in p, q, r), tau_Ps4, ip_Ps4, t3_ip_l/r, t4_ip. For S6 the parametrisation v(theta) is
  Ps4 j 0 1 theta (-theta^2/2); for S8, chi_1 = Ps4 j 0 1 0 0 and tau(v^3) = 12 q (p^2 + r^2) in these coordinates.

### Deviations from the write-up (all simplifications; none is a gap in the paper proof)
 - Prop R is proved for every y in L (not only those with row r = 0). rho = 0 by evaluating (5 + c rho) C(c) = 120 at c = -5/rho.
 - Coefficient extraction in Lemma C: evaluation at c = 1, -1, 2, -2.
 - S3/S4 use ONE generic element z of N (maxpt) instead of the forms l_m and the space K. Cases: three independent columns of z
   (caseA3: peel the other two columns), all columns on one line (A1), two lines (LemA2_proof: pattern (2,2) by peeling; patterns
   (2,3)/(3,2) contradict G23 evaluated at z). Singleton lines never need to be discussed. `peel`: finrank N <= 1 + finrank (N inf {col m = 0}).
 - (A1), case tau(v^3) != 0: pointwise x_m^3 = s x_m with s = p_2(x)/2; the support S of the generic element satisfies |S| s = 2 s.
 - (G23) coordinate-free, no WLOG v' = chi_1: v'^3 is isotropic, v perp v'^3 gives v in C v'^3 by (Q4), and
   [v'^3, v'^3, v', v'] = 8 kappa^2, kappa = tau(v'^4)/4 != 0.
 - (B-ii) by a dimension count: if S were nondegenerate and a column z_m of N nonzero, phi_m(K) would have dim 3 inside the
   2-dimensional space z_m^perp cap V.
 - (II-a) is proved in the form "v o v in C w and w o w in C v" (no row permutation, no zeta): coordinates p, q, r; if p1 = 0 or p2 = 0
   the bracket equals 8 r1^2 p2^2 resp. 8 p1^2 r2^2 != 0 (S11's point at infinity); otherwise t = q1/p1, u = q2/p2 and IIa_tu
   (the blueprint's ID7: 4(E(t,u) - E(u,t)) = (u-t)(4 + a^2 b + b^2), 4(E(t,u) + E(u,t)) = a(12 + a^2 b - b^2), a = 0 gives bracket -128)
   yields t^2 u^2 = 4 and 4 + t^4 + 4 t^3 u = 0, hence v o v = -(p1^2 t^3 / p2) w.
 - (II-b): <u, w^2> = 0 from T_e(Yu + W) + T_e(Yu - W) - 2 T_e(Yu) with W = w (e_c - e_d)^T in N; then u perp v, w and (Q4) twice.
 - The blueprint's types I/II/IV are not separate Lean definitions (draft in types.part, unused).

### Practical notes
 - Build: cd lean/fl; cat pre.part a.part b.part c.part d1.part e.part f.part g.part h.part j.part k.part o2.part p.part i5.part l2.part m.part n.part n.tail > FL.lean
   (pre: tools + P4; a: Stage A; b: Lemma C; c: B-i, Q1, Lemma N; d1: B-ii, Q4, B-iii, iso34; e: G23, generic points; f: A1;
    g: peel, maxpt, caseA3, caseLine, LemA_red; h: column permutations, pattern23, LemA2_proof; j: A1b, two_line_pattern, typeII_ids;
    k: A1cols; o2: S6_active; p: S8_elem, S8_step1; i5: tricho, HypS6/7/8, No22, SL_of, FL_of; l2: S7 reduction; m: IIa_tu, Ps4;
    n: proof of (II-a); n.tail: final theorem). This recipe reproduces FL.lean byte for byte.
   leancheck takes 45-170 s depending on load.
 - Lemma C is stated per deleted column m with the other columns m.succAbove 0..3; sa0..sa4 turn these into literals 0..4.
 - omega cannot identify two `finrank (sumZero 4)` atoms whose implicit arguments differ; use le_trans (see Bi).
 - `(Equiv.swap 0 2 * Equiv.swap 1 3) 0` does not elaborate without a type ascription; use a def (swp, swp0..swp4 by decide).
 - `-k * k'` is `(-k) * k'`; prove vector identities pointwise (funext; simp only [Pi.*]; ring / linear_combination).
 - Identities with i: never expand powers of i; keep j with hj : j * j = -1 and use Ps4_mul (certificate (a1 - a3)(b1 - b3) * hj).
 - Snapshots FL.v2 .. FL.v14.lean are all compiling states (v6: Lemma A complete; v9: S7 reduced to (II-a); v11: (II-a) proved;
   v12: HypS6 weakened by S6_active; v14 = final: S8 Step 1 proved and handed to HypS8).

STATUS 16:50: read brief/blueprint; plan = one file lean/fl/FL.lean built from parts (pre.part, a.part, b.part, c.part).
  Stage A (row expansion perm5_row, Prop R, stageA) written, first compile: 3 small errors, fixed, recompiling.
  Stage B part 1 (pc/tau/ip/t3/br, P4 -> column form, pc_expand, Lemma C = C1, C2, C34, C2pol) written, compiling.
STATUS 17:02: Stage A compiles (TA.lean exit 0). Lemma C (C1, C2, C34, C2pol) compiles. FL.lean v2 (adds B-i, Lemma N, Q1, B-ii, Q4, B-iii, types I/II/IV as defs, assembly from 5 hypotheses) compiling.
STATUS 17:03: FL.lean v2 compiles (exit 0, format 0): Stage A, Lemma C, Lemma N, Q1, Q4, B-i, B-ii, B-iii, root4/iso34, assembly from 5 hypotheses. Next: G23 core, generic-point lemmas, A1.
STATUS 17:13: FL.lean v3 compiles (adds root4k, pow4_iso, br_w3, G23core, G23, generic_t, generic_pt). Now A1 (g = 1 case of Lemma A: N inside v (x) C^5 has dim <= 2), compiling.
STATUS 17:19: FL.lean v5 compiles (exit 0): adds A1 (g = 1 case, dim <= 2), peel, maxpt (generic max-support element), perm_two/three, caseA3 (three independent column lines), caseLine, LemA_red: Lemma A reduced to LemA2 (two-line case). Final theorem now takes LemA2 instead of LemA. Next: prove LemA2 via column-permutation transport + G23.
STATUS 17:26: FL.lean v6 compiles (exit 0): LEMMA A (d <= 2) FULLY PROVED (LemA2_proof via column-permutation transport cperm/P4_perm/SLev_perm, pattern23 = G23 on the generic element). Final theorem now needs only HypS6, HypS7, HypS8 (the three cases of (q,d) = (2,2): >= 3 independent column lines / two lines / one line). Compiling v7: A1b (t3 != 0 => dim <= 1), two_line_pattern, typeII_ids, refined HypS7/HypS8.
STATUS 17:31: FL.lean v8 compiles (exit 0, format 0): A1b, A1cols, two_line_pattern, typeII_ids, refined HypS7/HypS8. RESULT section rewritten. Remaining budget used for S8/S7 preparation lemmas.
STATUS 17:37: FL.lean v9 compiles (exit 0, format 0): S7 reduced to the purely algebraic statement HypIIa (S7_elem, S7_step: <u,v^2> = <u,w^2> = 0 from C3 at the inactive column; HypS7_of, HypS7alg_of). Final theorem hypotheses now: HypS6, HypIIa, HypS8.
STATUS 17:41: RESULT rewritten for v9. Final file lean/fl/FL.lean = FL.v9.lean.
STATUS 17:53: FL.lean v11 compiles (exit 0, format 0): HypIIa PROVED (IIa_tu, Ps4 group-algebra coordinates, IIa_pqr, sq_Ps4, HypIIa_proof). S7 complete. Final theorem now has only two hypotheses: HypS6 and HypS8.
STATUS 17:57: FL.lean v12 compiles (exit 0, format 0): S6_active proved and handed to HypS6. Notes final. Remaining open: HypS6 (S6), HypS8 (S8).
STATUS 18:03: FL.lean v14 compiles (exit 0, format 0): S8_elem, S8_step1 proved; HypS8 now = S8 Steps 2-4. Notes final.
STATUS 18:04: done. Final file lean/fl/FL.lean (= FL.v14.lean), leancheck exit 0, format 0. Open: HypS6 (S6), HypS8 (S8 Steps 2-4). Reporting.
STATUS 18:13: ROUND 2 started (coordinator message: discharge HypS8 then HypS6; SL/FL stand-alone; column version). Plan: S8 Steps 2-4 coordinate-free via v-coordinates Qv (basis v, v^2, v^3 with v_i^4 = kappa; twisted convolution), no row permutation.
STATUS 18:20: resumed round 2 after a usage-limit pause; FLr.lean (= v14 + r1.part: Qv framework) compiles. Continuing with HypS8_proof.
STATUS 18:35: FL.lean v15 compiles (exit 0, format 0): HypS8 PROVED (S8 Steps 2-4: Qv framework r1.part, S8a/S8b/HypS8_proof r2.part). Final theorem now has the single hypothesis HypS6. Starting S6 (chart = special vector v avoiding all column lines; Qv coordinates with kap = 1; C3* ; patterns).
STATUS 18:57 (round 2): FL.lean = FL.v16.lean compiles (3818 lines, exit 0, format 0). Added t.part: SL6 (Lemma SL stand-alone, hypothesis HypS6 only), gap_swap5/trE5/FL_col_of (full free COLUMN version by transposition), cor_row / cor_row7 (corollaries of stage A + SL). Final theorem is now the conjunction SL + FL(row) + FL(column), single hypothesis HypS6. Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 t (.part) t.tail. Now writing S6 (chart via 6 special vectors + pigeonhole, U(theta) coordinates, C3* certificate, cases A/B/C).
STATUS 19:08 (round 2): FL.lean = FL.v17.lean compiles (4519 lines, exit 0, format 0). S6 reduced: chart (6 special vectors spv, pigeonhole over Perm(Fin 3)), U(theta) coordinates (Uv, lamL, N_coords), (C3*) certificate (star_cert, Lam_star), extension to all of N (Lam_F), algebraic core (AlgCore) with the singleton patterns (singA) and the (2,1,1,1) pattern (pairB) PROVED (core5, AlgCore_of, HypS6_of). The only remaining hypothesis is HypS6C = pattern (1^5) (theta injective), a pure statement about a submodule Lam of C^5. Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 t2 (.part) u.tail. Now doing pattern (1^5) via Mathlib Vandermonde (det_vandermonde_ne_zero_iff).
STATUS 19:13 (round 2): FL.lean = FL.v18.lean compiles (4759 lines, exit 0, format 0, axioms propext/Classical.choice/Quot.sound): HypS6C PROVED (pattern (1^5): mom3, Lam_ker, vdm3, roots5/moments5 via Matrix.det_vandermonde_ne_zero_iff, caseC_alg, HypS6C_proof). THE FINAL THEOREM HAS NO HYPOTHESES: Lemma SL + Theorem FL (row) + Theorem FL (column). Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 (.part) v.tail. Next: Lemma DS if time permits; then RESULT rewrite and report.
STATUS 19:16: ROUND 3 started (coordinator message: 2 h; targets (1) rows' DEFECT construction / normal form R1, (2) Lemma EQ + THEOREM SPLIT, (3) Lemma HYP, Hyperplane Lemma R4.1, SL_3, NCOL-S, (4) TC5 normal form). Lemma DS (chief; = converse half of R1 in the defect-0 case) is compiling as ds.part on top of v18.
STATUS 19:18: FL.lean = FL.v19.lean compiles (4928 lines, exit 0, format 0): chief's LEMMA DS proved (ds.part: P4_poly, P4_ones, DS_star, DS_i, LemmaDS: deletable row r => all row-r sums vanish; if moreover the row-r projection has dim 4 then L cap {row r = 0} is strongly level and finrank L <= 7). Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds (.part) v.tail. Round 3 next: defect construction (Prop. D), Lemma EQ, Theorem SPLIT.
STATUS 19:28 (round 3): FL.lean = FL.v20.lean compiles (5330 lines, exit 0, format 0). New: x1.part = rows' DEFECT CONSTRUCTION (Lev45, DefLine, defW K = (C(K)+C1)^perp as a submodule, defL r K = K (+) e_r (x) defW K; defL_level, defL_deletable, defL_finrank: finrank = finrank K + finrank (defW K); converse defect_conv: every level L has finrank L <= finrank L' + finrank (defW L'), L' = L.map (del r); defW_SLev: strongly level => defW = sum-zero) and verifyfl's LEMMA EQ (LemmaEQ, LemmaEQ_cols); x2.part = THEOREM SPLIT (ThmSplit: defect line C m, e_i m^T in K, <m,m> != 0 => K cap {<m, row i> = 0} strongly level and finrank K <= 4; via repl / P4_repl_add / per_rows / P4_sym = symmetry of the 5-linear form). Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 (.part) v.tail. Compiling x3.part: defC, finrank (defW K) + finrank (defC K) = 5, Hyperplane Lemma R4.1, Lemma HYP (a), (b).
STATUS 19:31 (round 3): FL.lean = FL.v21.lean compiles (5527 lines, exit 0, format 0). New x3.part: dotL (dot product as a map to the dual), defC K = span{C(Y)} (= C(L') + C1), defW_finrank: finrank (defW K) + finrank (defC K) = 5 (so dim W = 4 - e with e + 1 = finrank defC), defect_conv' / defL_finrank' (Prop. D with "4 - e"), HyperplaneLemma + HyperplaneCor (rows R4.1), LemmaHYP_a, LemmaHYP_b (verifyfl R3.3 (a), (b)). Next: SPLIT step (3) (ker kappa form), then SL_3.
STATUS 19:43 (round 3): FL.lean = FL.v22.lean compiles (5933 lines, exit 0, format 0). New y1.part: rows' LEMMA SL_3 in zero-row form (LemmaSL3: a strongly level 4x5 space with a zero row i has finrank <= 2) -- Vp_span/Vp_nondeg/Vp_t3/Vp_finrank (the plane V' = {tau = 0, x_i = 0}), SL3_q2 (q = 2 => N = 0, via Bii), SL3_two (two-line N: NEW SHORT ARGUMENT, C3 at the inactive column + C2pol cross conditions give <u,v> = <u,w> = 0, so u = 0; replaces R3.8(d)), SL3_d2 (d = 2 => q = 0). Compiling x4.part: THEOREM SPLIT in the ker kappa form (ThmSplit_kappa), via pc_ev / P4_repl_ones / P4_lin / split_id / split_ker.
STATUS 19:52 (round 3): FL.lean = FL.v23.lean compiles (6095 lines, exit 0, format 0). New x4.part: THEOREM SPLIT in the ker kappa form (ThmSplit_kappa: K cap {all column sums 0} is strongly level, finrank <= 3), i.e. step (3) of R3.1 (split_ker: column sums 0 => <m, row i> = 0), via pc_ev, P4_repl_ones (P4 b (row i := m, other rows 1) = 6 sum_{j != b} m_j), P4_lin (explicit linear coefficient of P4 b (1 + cY)), split_id (theta <m,m> = mu <m, y^i> in the form (C_b - 24) <m,m> = (D_i m)_b <m, y^i>). Build: ... x1 x2 x3 y1 x4 (.part) v.tail. Compiling n1.part: rows' Theorem NCOL-S (a) (R4.14).
STATUS 19:55 (round 3): FL.lean = FL.v24.lean compiles (6442 lines, 287 KB, exit 0, format 0). New n1.part: rows' THEOREM NCOL-S (a) (R4.14 (a)) PROVED: NCOL_S_a: DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K, m without zero entry => row i vanishes on N = K cap {<m, row i> = 0} and finrank K <= 3. Tools: kc1 / P4_poly1 / kc1_eq (explicit linear coefficient of P4 a (B + sY) = sum over rows k of P4 a (B with row k := row k of Y)), P4_zero_row, pc_ev2 / P4_repl2 (permanent with rows m, y, 1, 1), kc1_formula (= D^(1)(Y) m in the raw form 2 sum_{j != b} c_j sum_{l != b,j} m_l), split_eig (D_i(Y) m = mu m), ncol_lin (first-order eigenvector condition, by roots5), tau_repl0. Build: ... x1 x2 x3 y1 x4 n1 (.part) v.tail.
STATUS 20:00 (round 3): FL.lean = FL.v25.lean compiles (6593 lines, 295 KB, exit 0, format 0, GUARD 0/0). Guard rules adopted (coordinator message 19:56): helper namespace renamed to PEqualNP.Outside.L_gct_210_aux.FL (pre.part, v.tail), no line begins with add_ (defW rewritten as a structure instance with add_mem' mid-line; simp lists re-wrapped). New n2.part: NCOL-S (b): ncol_core (closed form D b = -2 S m_b + 4 c_b m_b - 2 c.m and the eigenvector relations), ncol_b1 (for every Y in K the column sums of the rows != i are equal on supp m), P4_zero_row', NCOL_S_b (m with exactly one zero n: row i of N is supported at n; N cap {row i = 0} strongly level, finrank <= 2, and = 2 if finrank K = 4). Build: ... x1 x2 x3 y1 x4 n1 n2 (.part) v.tail. Next (coordinator list): Theorem FS (z1.part written), TC5 normal form DI5.2, TC5, QB/PS/PR3, FL2*.
STATUS 20:04 (round 3): FL.lean = FL.v26.lean compiles (6783 lines, 304 KB, exit 0, format 0, guard 0/0). New z1.part: verifyfl's THEOREM FS (R3.2) in row form (ThmFS: defect space Cs inside 1^perp, e_i (x) Cs inside K, <,> nondegenerate on Cs => K cap {row i perp Cs} strongly level and finrank K <= 3 + finrank Cs; fsMap = the map K -> Dual Cs). New z2.part: TC5 NORMAL FORM DI5.2 (uY, dY, e2, Ed; TC5_sum, TC5_diff, TC5_n2/n3/n4 = the four displayed identities, TC5_dd = perm[d,d,1+a,1+b] = 4 e_2(d) + 2<a+b,E(d)> + perm[d,d,a,b] (holds for all a, b), TC5_normal: DefLine K (e_0 - e_1) <=> (i) and (ii)). Build: ... n1 n2 z1 z2 (.part) v.tail. Compiling q1.part: verifyfl's LEMMA QB (R4.1).
STATUS 20:08 (round 3): FL.lean = FL.v27.lean compiles (6932 lines, 315 KB, exit 0, format 0, guard 0/0). New q1.part: verifyfl's LEMMA QB (R4.1): qA1, qA2 (explicit linear and quadratic coefficients of P4 b (1 + cY)), P4_quad, qb_lin (m b' A_k(b) = m b A_k(b') for k = 1, 2, by roots5), qA1_eq, qA2_eq (closed forms), LemmaQB: DefLine K m, sum m = 0, m != 0, Y in K => exists kappa theta2 with column sums = kappa m, (a) sum_a <y_a,y_a> = <s,s> + kappa^2 <m,m>, (b) <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(theta2/2) m_j for all j (the form before centring). Build: ... z1 z2 q1 (.part) v.tail. Compiling r4.part: Lev45_quad (QB (a) for every level 4x5 space), rows' R4.2 (a), (b) (single-row parts lie in the defect space and are pairwise orthogonal).
STATUS 20:10 (round 3): FL.lean = FL.v28.lean compiles (7050 lines, 321 KB, exit 0, format 0, guard 0/0). New r4.part: Lev45_quad (for every level 4x5 space: total sum 0 and sum_a <y_a,y_a> = <s,s> + sum_a c_a^2), rowE, one_add_rowE, one_add_rowE2, single_row_sum, single_row_perp, single_row_defC (rows' R4.2 (a), (b)). RESULT section rewritten. Build: ... z1 z2 q1 r4 (.part) v.tail. Next: R4.2 (c) (r5.part).
STATUS 20:15 (round 3): FL.lean = FL.v29.lean compiles (7106 lines, 325 KB, exit 0, format 0, guard 0/0). New r5.part: rows' R4.2 (c) (single_row_t3: e_i u^T, e_k u'^T, e_l u''^T in a level K with i, k, l distinct => sum_j u_j u'_j u''_j = 0), proved WITHOUT a three-row permanent: additivity in row l + symmetry P4_sym reduce it to sum_b u''_b P4 b (rows 1+u, 1+u', 1, 1) = 0 and P4_repl2. Build: ... q1 r4 r5 (.part) v.tail. Compiling f1.part: FL45 (a 4x5 level space containing a full free row has finrank <= 6; rows' corollary of SL_3 / FL2* (c)).
STATUS 20:21 (round 3): FL.lean = FL.v30.lean compiles (7221 lines, 330 KB, exit 0, format 0, guard 0/0). New f1.part: FL45 (a 4x5 LEVEL space containing the full free row e_i (x) 1^perp has finrank <= 6; = rows' corollary of SL_3 and FL2* corollary (c); the 4x5 analogue of Theorem FL): zrow (zero out row i, linear), one_add_zrow, FL45_core (the deletion vector of (Y with row i := ones) is constant and (5 + rho) g = 120), FL45. Build: ... q1 r4 r5 f1 (.part) v.tail. Compiling g1.part: rows' R4.15 (F1), (F2) (first-order constraints from single-row elements, any e).
STATUS 20:26 FL.v31 compiled (exit 0, guard 0/0, format 0): g1.part = rows R4.15 (F1),(F2): Di_mem, R415_F1, R415_F2. Next: h1.part (SLev_Lev45, DefLine_Lev45, SLev_DefLine, NCOL_S_neutral, LemmaZ1).
STATUS 20:31 FINAL STATE: FL.lean = FL.v32.lean (7451 lines, 341940 bytes; leancheck exit 0 in about 4.5 min, axioms propext / Classical.choice / Quot.sound, guard 0/0, format 0): h1.part = SLev_Lev45, DefLine_Lev45, SLev_DefLine, NCOL_S_neutral, LemmaZ1. Coordinator: stop here, work moves to the local session; handover written to handover/HANDOVER-leanfl.md. No new lemmas started (a planned i1.part with Lemma Z (Z2) was NOT written).

## ROUND 4 (leanfl, new agent on Kevin's machine; start 19:40 UTC machine clock). Targets: (1) guard compliance + recompile; (2) verified lemmas on the
## defect-inequality route (Theorem PS normal form -> rows' NCOL-P3; then P51 / NCOL2-P / PR-RED / PR3 as time allows).
 Guard finding: FL.lean (= FLi = v31) already had namespaces and add_ lines right (leancheck guard 0/0); the PROJECT guard
 (outside-guard.mjs imports) refused it for ONE reason: the last theorem was named PEqualNP.Outside.L_gct_210_fl, but at the top level
 only `theorem PEqualNP.Outside.L_gct_210` may stand. Fix: w.tail = v.tail with the name PEqualNP.Outside.L_gct_210 (statement unchanged:
 SL /\ FL row /\ FL column; it is a placeholder, not the gap statement). FLk.lean = parts through h1 + w.tail: project guard passes.
 Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1 (.part) w.tail
STATUS 19:52 (machine clock, UTC): FLk.lean (guard-fixed tail + h1.part) compiling; project guard on FLk passes. Writing ps.part (Theorem PS normal form).
STATUS 20:08: machine heavily loaded (load 40, msolve/Singular jobs); FLk compile still running (slow). Written: ps.part (QBc, phi_onto, pol_alg,
  PS_pol, PS_f, PS_nf = verifyfl's THEOREM PS (a) normal form; np3_col, np3_X, np3_alg, NCOL_P3_core = rows' THEOREM NCOL-P3 three-column case),
  ps2.part (QBc_of, ThmPS_a, NCOL_P3 with DefLine), ps3.part (rs_cperm, DefLine_perm, NCOL_P3_perm: any three active columns via a column
  permutation). Small test file leanfl/Tps.lean = pre a b c ps (QB enters as the hypothesis QBc, discharged by LemmaQB in ps2) queued.
STATUS 20:05: FLk compile at 19 min wall (lean gets ~50% of one core under load 40; leancheck's limit is 25 min). Written ps4.part:
  sq_prop (m_j^2 X = lam m_j for all j, sum m = 0, m != 0 => X = 0; 32-case split) and ThmPS_b (verifyfl PS (b): <f,f> = (3/4) kappa^2 in my
  normalisation z_j = (kappa m_j/4) 1 + m_j phi_j(Y_f), f = s(Y_f); PS's own normalisation has 2 B_j f_Z = -phi_j(Y_f), <f_Z,f_Z> = 3 kappa^2/16).
  FLl.lean = FLk parts + ps ps2 ps3 ps4 + w.tail assembled (7878 lines, 362 KB; format 0, project guard passes).
STATUS 20:07: all hand-computed linear_combination certificates of ps.part re-checked with sympy (leanfl/chk_ps.py: 0 residue). ps5.part (ThmPS_c, principal stratum dim <= 5) written; FLl = ... ps ps2 ps3 ps4 ps5 + w.tail (8000 lines, 368 KB). handover/HANDOVER-leanfl.md drafted. Waiting for FLk.
STATUS 20:14: FLk compile KILLED by leancheck's 25-min limit (exit 124, 1501 s, peak memory only 0.84 GB): the machine is swapping
  (free 0.3 GB, available 3.2 GB, swap 2.6 GB used, si/so active; msolve + five Singular jobs hold ~6 GB). This is not a Lean error:
  the same file content (FLi + new tail + h1) is not refuted, only not finished. Full-file compiles (8.4 GB) are not possible until RAM
  frees up. Small test Tps.lean (pre a b c ps, ~1000 lines) got the slot at 20:11.
STATUS 20:38: (1) NOTES merged with the cloud's final copy (the 21 missing lines: RESULT block rows for r5/f1/g1/h1 and STATUS 20:31 =
  FL.v32 = FLj COMPILED in the cloud, exit 0, 4.5 min, standard axioms); my round-4 section kept below it (pre-merge copy:
  leanfl/NOTES-leanfl.before_merge.md). So h1.part is already Lean-checked; FLk = FLj with the renamed tail.
  (2) Tps.lean (small test) also hit the old 25-min limit with peak 0.84 GB and NO output: Lean never finished importing Mathlib under
  swapping, so nothing is known yet about ps.part. leancheck limit is now 60 min; FLk re-queued (behind leanzbf's R4b), then Tps2.
  Restructured: ps4/ps5 now take QBc (PS_b_core, PS_c_core), DefLine wrappers ThmPS_b / ThmPS_c in ps2; build order ... h1 ps ps4 ps5 ps2 ps3.
  Tps2.lean = pre a b c + colsumL snippet + ps ps4 ps5 (tests all new proofs except the DefLine wrappers and ps3).
STATUS 20:45: RESULT ROUND 4 block added at the top. ncolp.part (NCOL-P core, sc_key, phi_colE, rs_colE) + np3b.part (two/one-column NCOL-P3) + wrappers written and sympy-checked (leanfl/chk_np3b.py, chk_ncolp.py). FLl = 8287 lines. FLk2 still waiting for the slot (R4b thrashing: 0.7 GB available). Tps2 queued after FLk2.
STATUS 20:49: ps.part hdec: the four fin_cases goals now closed by explicit show + ring / linear_combination (no simp normal-form dependence). handover/HANDOVER-leanfl.md = cloud handover + section 6 (round 4). Machine: swap 8.1/8.2 GB full, 0.77 GB available; R4b (leanzbf) holds the slot; coordinator alerted by message.
STATUS 21:04 ROUND 4 END: no Lean run could finish this round (machine memory-starved; R4b of leanzbf held the slot from 20:36). A DETACHED compile chain is running: leanfl/run_chain.sh = leancheck FLk.lean -> leanfl/FLk3.log, then leancheck leanfl/Tps2.lean -> leanfl/Tps2.log, then (only if Tps2 exit 0) leancheck lean/fl/FLl.lean -> leanfl/FLl.log; leanfl/chain.done is written at the end. Unfinished PR-RED draft (contains a placeholder, NOT a part): leanfl/prred.draft. Final report sent.

## ROUND 5 (leanfl; start 21:07 UTC). Targets: (1) read chain logs (FLk3, Tps2, FLl) and repair; (2) PR-RED (R4.4), PR3 (R4.5);
## (3) rows' T3 / Lemma O3 and SC1 (R5.6); (4) P51, NCOL2-P.
STATUS 21:07: chain still waiting for the slot (R4b compiling). Reading T3 / Lemma O3 (rows) and the verify2 ledger.
STATUS 21:12: prred.part written (rowE_rs, rowE_colsum, tau_col_colsum, PR_RED_core = verifyfl PR-RED R4.4 with the hypothesis 'every 4-dim K' <= K containing H, not column-centred, contains some e_i m^T'; pigeonhole over t in Fin 5); PrincNS4 + PR_RED (DefLine wrapper) in np3c. ps5 refactored: PS_N0_le and QB_map_rs are now lemmas. The chain's test file leanfl/Tps2.lean now = Tps3 (adds prred + rowE snippet). FLl = 8430 lines, 389 KB, guard 0. T3/Lemma O3: read; the hand proof goes through SL_2 = Spin(3) and Choi ranks - not a quick formalization; postponed behind SC1.
STATUS 21:21: SC1 (rows R5.6) written: sc1a.part (sc1F, rs_col, sc1_polar = polar of the degree-2 coefficient qA2 between Y and x e_n^T, 25 literal cases, maxHeartbeats raised by the allowed set_option; sum_ite_ne5) and sc1b.part (qA2_sum, qA2_defC: degree-2 coefficient vector lies in defC via 5-point weights (35,-104,114,-56,11)/24; SC1: <x, s(Y) - y_n> = 0 and (<x,y_b>)_{b != n} (0 at n) lies in defC K, any Lev45 K, any column n). Polar formula sympy-checked for all 25 (n,b) (leanfl/chk_sc1.py). Tps2.lean now also tests sc1a. FLl = 8551 lines, 394 KB, guard 0. Chain still waiting (R4b holds the slot).
STATUS 21:28: coordinator: Lean compiles move to a dedicated window (~22:30 UTC). I STOPPED my queued chain at 21:25 (it would have starved into the window); leanfl/run_chain.sh (FLk -> Tps2 -> FLl if Tps2 passes) is ready to launch when the window opens. New since 21:21: pr3a.part (iso_triple: three isotropic sum-zero vectors adding to 0 are proportional; pc_neutral3: pc(1+a v,1+b v,1+c v,1) = 24 + 2abc t3(v) for tau v = <v,v> = 0, certificate sympy-checked leanfl/chk_pr3a.py; P4_neutral3) and pr3b.part (PR3_step1 = verifyfl R4.5 step (1): in a principal setting with 3-support m on columns 0,1,2 a column-centred Zs != 0 in ker s has columns v, s v, t v, 0, 0 with v isotropic, tau v = t3 v = 0; DefLine wrapper PR3_step1_def in np3c). Robustness edits: rw-then-rfl replaced by exact (ps.part hp, sc1a rs_col, pr3a hb); an add_ line-start in pr3a fixed (guard caught it). FLl = 8688 lines, 401 KB, guard 0; Tps2 = 1894 lines (pre a b c d1 + 3 snippets + all new core parts).
STATUS 21:29: handover section 7 written (round-5 parts, window procedure, detailed PR3 plan via the existing Qv tools, T3 assessment). Waiting for the coordinator's Lean window.
STATUS 21:33: ps6.part (phi_inj; PS_bil = polar of PS (b): <f_Z, f_Z'> = 3 kappa kappa'/4, via Y_{Z+Z'} = Y_Z + Y_Z') and pr3c.part (PR3_step2 = verifyfl R4.5 step (2) in the existing Qv coordinates: centred columns of Z are Qv v 0 p_j (beta m_j) 0 with 16 kap beta^2 = 3 and sum p_j = 0; sign argument by three explicit certificates) written. pr3c needs r1.part, so it is only in FLl (not in Tps2). leanfl/build.sh rebuilds FLk, FLl (8876 lines, 410 KB, guard 0) and Tps2 (1953 lines) from the parts; run_chain.sh compiles them in the window.
STATUS 21:41: THEOREM PR3 (verifyfl R4.5) fully written: pr3d.part (tau/ip/t3/pc with a zero vector; pc_Qv3 = the 4x4 permanent with three Qv columns, via pc_expand + Qv_mul/ip_Qv; pr3_alg = 2x2 Lagrange-identity certificate det*Q(p)^2 in (Q(l), B(p,l))) and pr3e.part (PR3_core: QBc + 3-support m on columns 0,1,2, <m,m> != 0, neutral column 3, principal H => finrank K <= 4; route: elements Zs, Z1 of ker s as in PR-RED, step 1, kap = v_0^4, step 2, the cubic C_3(Z1 + b Zs) - 24 = 8 kap beta Q(p + b l) - (3/4) e3 (certificate from sympy, leanfl/chk_pr3e.py), b = 0, 1, -1 give Q(l) = 0, B(p,l) = 0, pr3_alg gives Q(p) = 0, hence e3 = 0: contradiction); DefLine wrapper PR3 in np3c. All certificates sympy-checked (chk_pr3d.py, chk_pr3alg.py, chk_pr3e.py). FLl = 9096 lines, 421 KB, guard 0. Tps2 unchanged in scope (no r1-dependent parts).
STATUS 21:45: coordinator's Lean WINDOW 1 armed (/home/kevxhk/work/runs/leanwindow1b.sh): it compiles FLk -> leanfl/FLk_w1.log, Tps2 -> Tps2_w1.log, FLl -> FLl_w1.log (if Tps2 passes). My run_chain.sh is NOT used. Files frozen until the window has copied them (FLk 7451 lines, Tps2 1953, FLl 9096). Repair from the w1 logs afterwards.
STATUS 22:25 WINDOW 1 RESULTS (coordinator): FLk.lean COMPILED on this machine: exit 0, 0 errors, axioms propext / Classical.choice /
  Quot.sound, peak 6.2 GB (1833 s, mostly thrashing). => the GUARD-COMPLIANT FL strand with final theorem PEqualNP.Outside.L_gct_210 is
  Lean-checked (7451 lines, 341937 bytes; project guard passes). Tps2.lean: exit 1 with exactly 2 errors, both in NCOL_P_core (ncolp.part):
  in `∃ n x, x ≠ 0 ∧ (fun p => if p.2 = n then x p.1 else 0) ∈ H ∧ ...` the binder x was elaborated as ℕ (from `x ≠ 0`). Everything
  else in Tps2 compiled: sc1a (sc1_polar, 25 cases), ps (PS normal form, NCOL_P3_core), ps4 (sq_prop, PS_b_core), ps5 (PS_c_core),
  np3b (two/one-column NCOL-P3), ncolp up to sc_key, prred (PR_RED_core), pr3a, pr3b (PR3_step1), ps6 (PS_bil).
  FIX: binders annotated `∃ (n : Fin 5) (x : V4)` and `∀ (n : Fin 5) (x : V4)` in ncolp.part and np3c.part; files rebuilt
  (FLl 9096 lines). Still untested: sc1b (SC1), pr3c/pr3d/pr3e (PR3 steps 2-4), and the DefLine wrappers ps2/ps3/np3c.
  leanfl/window_files.txt for WINDOW 2 (~01:00-02:00 UTC) lists FLl.lean only (it contains everything; errors stay localized).

## ROUND 6 (leanfl; start 22:32 UTC). Targets: (1) P51 (R5.11); (2) NCOL2-P (R5.13); (3) X5 / PR5 wrappers with the exact Groebner
## parts as explicit hypotheses; (4) Lemma Z / TC5. Assemble into FLm.lean (= FLl + new parts) for window 2 if ready.
STATUS 22:27: lz.part written (e2b, Edb, pc_F_expand [4 pc expansions, maxHeartbeats raised], LZ_pair_alg, LZ_shift, LZ_pair, LemmaZ = verifyfl Lemma Z (Z1) second half eps(D,zeta) = 0 and (Z2) for z = z' for all three column pairs; certificates sympy-checked leanfl/chk_lz.py, chk_lzalg.py). FLm.lean = FLl + lz (9223 lines, 427 KB, guard 0); window_files.txt now lists FLm.lean. Small test leanfl/Tlz.lean (pre a b c + DefLine + z2 + zE snippets + lz, 981 lines).
STATUS 22:29: lzp.part (zE_add, Ed_pol, pc_pol, LemmaZ_pol = (Z2) polarised in z, z') added; FLm = 9266 lines. Next: P51 part (i) first step = rank-one law Z = a m^T for kernels closed under taking single columns (rows R5.11 proof of (i) / R5.12 rigorous part for e = 1).
STATUS 22:37: P51 pieces written: p51a.part (cE, cE_sum, P51_rank1: for a principal H closed under taking single columns, every Z in ker s is a m^T with a = kappa/4 - f; = R5.12 rigorous part for e = 1) and p51b.part (E2v, e3v, E3v, pc_add4, pc_x4, cubic4, P51_deriv4: Z = a m^T and x e_4^T in K, m injective => <x,E_2(a)> = <x,E_3(a)> = 0 (no case m_n = 0 needed); pair_sq, P51_unit: E_2(a), E_3(a) constant => a constant or all pairwise products 0, via an explicit radical certificate (a0 a1)^2 in (e2(a_{-i}))). Certificates sympy-checked (leanfl/chk_p51.py, chk_p51u2.py). Now: assembly P51_i (transport to column 4, X_n span V, dimension count).
STATUS 22:40: p51c.part written: P51_deriv (any column n, by transport with Equiv.swap n 4), pw_dim (a subspace of C^4 whose vectors have pairwise-zero products has dim <= 1), P51_key, P51_i = rows THEOREM P51 (i): distinct entries of m + principal H closed under taking single columns (types (1,1,1), (2,1), (3)) => finrank K <= 4. FLm = 9722 lines (guard 0). Now P51 (ii) (two-column kernels).
STATUS 22:44: P51 COMPLETE in Lean text: p51d.part (two_rel, span2_perp, P51_ii_core = rows P51 (ii): two-column principal H with m_a != m_b and dim N >= 2 is a full free column; cc_of_single; P51_two: distinct entries + two-column H => finrank K <= 4 (via (ii) then (i)); P51_two_perm: any two columns). Together with P51_i (column-closed H: types (1,1,1), (2,1), (3)) this is rows' THEOREM P51: no (5,1) space with distinct entries and a principal kernel of type (1,1,1), (2,1), (3) or (3,2). hc0 certificate sympy-checked (leanfl/chk_p51d.py). FLm = 10076 lines, 467 KB, guard 0; window_files.txt -> FLm.lean.
STATUS 22:45: RESULT ROUND 6 block + handover section 8 written. Round-6 deliverable: FLm.lean queued for window 2.
STATUS 22:46: x5a.part (rank1_col = rows R7.3 step (1) first claim: a rank-one column of a principal H is the orthogonal projector onto a non-isotropic line, col Y c = (<s(Y),v>/<v,v>) v) added (also in Tps2). FLm = 10125 lines, 468 KB, guard 0. ROUND 6 END: FLm.lean is the window-2 file (leanfl/window_files.txt); everything new since FLk (rounds 4-6) awaits that compile.

## ROUND 7 (leanfl; start 22:57 UTC). Targets: (1) rest of X5's hand part (B_a = R, B_b = -R on v^perp); (2) TC5 (P1)-(P4) on
## LemmaZ / LemmaZ_pol; (3) NCOL2-P if an e = 2 PS is clean; (4) other verified items. Appended as FLn.lean (= FLm + new parts).
STATUS 22:49: x5b.part written: X5_struct (rows R7.3 step (1): for a principal H on columns 0,1,2 whose column 2 is the projector onto the non-isotropic line Cv, the element of H with row sums v is v e_2^T, i.e. B_a v = B_b v = v; proof: w = col 0 of Y_v is isotropic and orthogonal to v, and the 2-dim image phi_0(H cap {<s,v> = 0}) is orthogonal to span{v, w}, so w = 0 by perp_sup_one) and X5_perp (on v^perp: column 2 vanishes, phi_1 = -phi_0 (B_b = -B_a), and phi_0 maps into v^perp). Certificates sympy-checked (leanfl/chk_x5b.py). FLn.lean = FLm + x5b (10266 lines; guard 0); FLm unchanged (md5 98575d75...).
STATUS 22:52: tc5c.part (X2c, X3c, pc_expand2, pc_dd_scale, TC5_deg_pair, TC5_deg_i, TC5_degree = DI5.2's degree-wise conditions (C1')-(C4') for [u,y_2,y_3,y_4] and the three pair conditions: degree 1 sums, degree 2 X2c = 4 e2(d) (= qbar_1 = Q(d)), degree 3 X3c = 2<y_k+y_l, E(d)>, degree 4 [u,u,y_k,y_l] = perm[d,d,y_k,y_l]); pc_dd_scale sympy-checked (leanfl/chk_tc5c.py). FLn = 10398 lines.
STATUS 22:52: window_files.txt switched to FLn.lean (10376 lines, 481 KB; = FLm byte-identical prefix + x5b + tc5c; guard/format 0).
STATUS 22:55: RESULT ROUND 7 block + handover section 9 written. Round-7 deliverable queued as FLn.lean for window 2.
STATUS 23:02: x5c.part written: X5_fv, X5_mc = rows R7.3 step (2), first conclusion, in a SHORTER form: in a (5,1) space (dim N >= 2) whose principal H has the rank-one column c (projector onto non-isotropic Cv), m_c = 0 -- WITHOUT the case split on m_a, m_b and WITHOUT VF-A/TC5. Argument: if m_c != 0, pairing the row-sum relation with v gives <f_W, v> = 0 for every W in N (2 m_c <f,v> = 0, using B_a v = B_b v = v); so v is orthogonal to f_Z (non-isotropic) and f_Zs (isotropic, nonzero, orthogonal to f_Z), hence v is in C f_Zs (span2_perp) and isotropic: contradiction. [Flag for verify2/rows: this replaces the R-scalar / VF-A sub-cases of step (2).] FLn = 10523 lines (guard 0); FLm unchanged.
STATUS 23:04: lagcore.part (LAG_core: the algebraic heart of verifyfl Lemma LAG (a): for z0 in V isotropic nonzero and tau z1 = 1, the relations E(z0,z1) = z0 o (z1 - 1/2) = lam z0^2 and E(z1) = z1 o (z1 - 1) = mu z0^2 are contradictory; 16 support cases generated by script, certificates sympy-checked) appended. FLn = 10568 lines, 490 KB, guard 0; window_files.txt -> FLn. ROUND 7 END (report sent).

## ROUND 8 (leanfl; start 23:10 UTC). Targets: (1) LAG (a) from LAG_core, LAG (b); (2) NB; (3) TC5 (P1); (4) rest of X5 step (2).
## New parts go into small test files until window 2 has compiled FLn (then FLo.lean).
STATUS 23:08: lag.part written: tau_Ed, tau_Edb, perp2, LAG_a (verifyfl Lemma LAG (a) in the form needed by (P1): if zeta = C z0 + C z1 is Q-isotropic (z0 in V nonzero, tau z1 = 1), every subspace P of V orthogonal to E(z0), E(z0,z1), E(z1) has dim <= 1; via LAG_core), LAG_b (Lemma LAG (b): no chi_1-type n (n_i^4 = kap != 0, tau n = <n,n> = t3 n = 0) is orthogonal to both E(z0) and E(z0,z1); proof in the Qv coordinates of r1.part). Small test file leanfl/Tlag.lean (pre a b c d1 + e2/e2b/Qv snippets + lagcore + lag, 1237 lines) prepared for the next window.
STATUS 23:18: NB written. nbcore.part (generic, only needs pre a b c d1): neutral_pol, neutral_iso (B_j isometric: <phi_j Y, phi_j Y'> = <s(Y), s(Y')> from exact qbar_j = 0), neutral_perp (<z_j, B_j sigma> = 0 for s(Z) = 0), neutral_zero (q = 3 => z_j = 0), iso_perp_plane, neutral_zero2 (S contains a nondegenerate plane => z_j = 0). nb.part (mTC wrappers): mTC_vals/sum/ne, TC5_tau (tau u = tau y_j = tau s = 0), NB_qbar ((C2') qbar_3 = qbar_4 = qbar_5 = 0 from TC5_degree + TC5_deg_i; certificate sympy-checked, leanfl/chk_nb.py), NB3 and NB_plane (Lemma NB: q = 3, or S containing a nondegenerate plane => Nbar = 0, i.e. s(Z) = 0 => y_2 = y_3 = y_4 = 0 and u = 0). leanfl/build8.sh builds lean/fl/FLo.lean (= FLn parts + lag nbcore nb; 11018 lines, guard-clean) and leanfl/Tr8.lean (small test: pre a b c d1 + snippets + lagcore lag nbcore; 1396 lines, guard-clean). FLn.lean untouched (md5 19de0ab6...). Next: TC5 (P1) building blocks.
STATUS 23:23: TC5 (P1) building blocks written in lean/fl/p1.part (+ TC5_qbar1 in nb.part): zE_smul, dY_zE, e2_ip; LAG_line (E_zeta^perp cap V is contained in a line C n; from LAG_a); zeta_span (d with eps(d, zeta) = 0 lies in zeta, zeta = C z0 + C z1 Lagrangian; via span2_perp); P1_D (D inside zeta, from LemmaZ); P1_line (all neutral columns of L' lie on one line C n; from LemmaZ, LemmaZ_pol, TC5_tau, LAG_line); P1_nf (normal form z0 in zeta cap V nonzero, tau z1 = 1, from two independent zeta vectors; the case zeta inside V excluded by Q4); TC5_qbar1 (qbar_1 = <u,u> - <s,u> = 2 e2(d), i.e. Q = 2 e2). All linear_combination certificates sympy-checked (leanfl/chk_p1.py, chk_nb.py). FLo.lean now = FLn parts + lag nbcore nb p1 (11238 lines, guard-clean). Remaining for (P1): the case analysis on n (non-isotropic: c = 0..3 nondegenerate-form bounds; isotropic: needs S4 (A1) + LAG_b).
STATUS 23:37: TC5 (P1) complete in Lean source (p1b.part: uYL/dYL/mL, uY_dY_zero, P1_L, P1_Lfacts, iso_image, P1_van, line_quad, prod_lin, eps_of, line_exp, P1_rel, P1_aniso, P1_reduce; p1c.part: chi_pow, iso_quad, L_slev, P1_iso, TC5_P1). LAG_line/P1_line now also return tau n = 0 and n perp E(z0), E(z0,z1), E(z1). RESULT ROUND 8 block added at top. FLo.lean rebuilt (11764 lines). Next: self-review of the new parts for elaboration risks; window_files.
STATUS 23:39: handover section 10 written; Tr8 extended with the generic P1 lemmas (1716 lines) and listed as optional 2nd entry in window_files.txt (after FLn). Self-review of idioms against compiled code (Q4/Bi patterns, Mathlib names finrank_lt_finrank_of_lt, finrank_mono, mem_span_insert, mem_span_range_iff_exists_fun, finrank_range_le_card, finrank_bot checked in the local Mathlib source).
STATUS 23:42: TC5 (P2) written (p2.part: two_indep, zeta_le_one, Z_of_nbar, rs_le3, no_nbar, TC5_P2). FLo = FLn parts + lag nbcore nb p1 p1b p1c p2 (11880 lines). New tool leanfl/closure.py: dependency closure of the R8 parts -> leanfl/Tr8full.lean (2775 lines, guard 0), now the optional 2nd entry of window_files.txt (replacing Tr8). Waiting for window 2 (FLn) log.
STATUS 23:44: nbl.part (neut_facts, NB_line: the neutral columns of K cap ker s span a totally isotropic subspace, dim <= 1; line_of_le_one; NB_lines: each neutral column of Nbar lies on an isotropic line C v_j with tau v_j = 0 = <v_j,v_j>) -- the S5 input of TC5 (P3)/(P4). R8 = lag nbcore nb p1 p1b p1c p2 nbl; FLo/Tr8full rebuilt.
STATUS 23:47: RESULT ROUND 8 block final for now; waiting for the window-2 (FLn) log; no compile started by me.
STATUS 23:49: nbq.part (pc_full, nbar_tau, nbar_cubic, nbar_quartic, nbar_eqs: the (P3) cubic/quartic of Nbar from the u-deletion; leanfl/chk_nbar.py exact). R8 = ... nbl nbq; FLo 12019 lines, Tr8full 2916 lines, guard 0. FLn untouched.
STATUS 23:49: ROUND 8 report sent (window-2 log not yet in; FLn unchanged, md5 19de0ab6...). Next on return: repair from the window-2 log, then FLo / Tr8full.

## ROUND 9 (leanfl; start 23:51 UTC). Targets: (1) repair FLn / Tr8full from the window-2 logs (fixes as small part files ->
## FLo); (2) TC5 (P3): exact classification of isotropic pairs in V with tau(v w^2) = tau(v^2 w) = 0 WITHOUT the bracket condition
## (Singular over Q, < 0.5 GB, background, calibrated); (3) TC5 (P4) branches.
STATUS 00:03: (P3) classification DECIDED exactly (Singular over Q(I), leanfl/sing9, < 1 s, calibrated; COMPUTE-leanfl.md round 9): related isotropic pairs = 3 chi_1-type pairs (one S_4-orbit, contains (chi_1,chi_3)) + 4 zero-row pairs; 14 distinct lines, each in at most one pair => no triangle. vs verifyfl DI5.3 (P3): ONE MORE chi_1-type pair than the paper's list (same S_4-orbit; no new branch needed). Lean route WITHOUT Groebner certificate: p3a.part (generated by leanfl/gen_rel.py with sympy-checked certificates): pair_E2 (6 y_k^2 - 2 g y_k independent of k, from Newton for u = v + s w), pair_rel (v o w = (g/4) 1, or a common zero coordinate k with 3 v_m w_m = g for m != k); p3b.part: ip_ne_of_line, rel_prop, no_triangle, two_equal (3 tau(v^2 w^2) - <v,w>^2 != 0), three_equal. New test file leanfl/Tr9.lean (closure of p3a p3b, 520 lines). FLo += p3a p3b. Tr8full frozen (window 2).
STATUS 00:08: window 2 started 00:05 (leanfl/FLn_w0005.log, empty so far = compiling). TC5 (P3) written: p3c.part (cubN, quaN, nbarL (Ybar-map Z -> (y_3,y_4,y_5)), symmetry lemmas, cub_rels, cub_two, quart_two, three_rels, fin_le_two, smul_mul_eq, TC5_P3 : finrank ((K cap ker s).map nbarL) <= 2, i.e. dim Nbar = 3 is impossible; route = NB_lines (isotropic lines v_j, all nonzero by a dimension count), realisation of all (l_3 v_3, l_4 v_4, l_5 v_5), nbar_eqs, then three distinct lines -> no_triangle, two equal -> two_equal, three equal -> three_equal). Certificates leanfl/chk_p3c.py. R9 = p3a p3b p3c; Tr9.lean (closure, 1525 lines) and FLo (= FLn parts + R8 + R9) rebuilt; Tr8full / FLn untouched.
STATUS 00:12: p4a.part (nbar_ker, TC5_dims: finrank K >= 5 => finrank K = 5, q = 2, dim Nbar = 2, zeta != 0 = the (P4) configuration). R9 = p3a p3b p3c p4a. Handover section 11 written. FLn compile running (window 2).
STATUS 00:12: classification calibrated a second time (with bracket: only the 4 zero-row pairs, = Lean HypIIa). Waiting for FLn log (background watcher).
STATUS 00:14: p4b.part (S_radical: in the (P4) configuration S = s(K) has an isotropic radical vector n0 != 0 in S, S inside n0^perp -- the 'S = n0^perp' of (P4)). R9 = p3a p3b p3c p4a p4b. FLn compile still running (log streaming warnings, 0 errors so far); error locator leanfl/locate.py ready.
STATUS 00:15: WINDOW 2 RESULT FLn: exit 1 but only 12 errors, all in lagcore.part (postponed exponent in pow_eq_zero_iff); fixed (n := 2), certificates re-checked; backup leanfl/lagcore.part.bak_w2. Waiting for Tr8full log.
STATUS 00:22: WINDOW 2 RESULT Tr8full (all round-8 parts, 2916 lines, 360 s, 5.7 GB): exit 1 with 13 errors = the 12 LAG_core ones (already fixed) + 1 in line_of_le_one (finrank_span_singleton without type ascription: field stuck) -> fixed in nbl.part, same latent bug fixed in p4b.part. So ALL of round 8 (LAG a/b, NB, TC5 (P1) incl. P1_aniso/P1_iso/TC5_P1, TC5 (P2), nbar equations) elaborates. window_files.txt now lists FLo.lean (12.6k lines, all fixes + round 9) and Tr9.lean for window 3.
STATUS 00:22: ROUND 9 report sent (repairs done; FLo + Tr9 ready for window 3).

## ROUND 10 (leanfl; start 00:25 UTC). Targets: (1) TC5 (P4) branches (shared lemmas first); (2) parts testable alone via
## closure.py (Tr10 next to FLo in window 3); (3) decide imprecise facts exactly (Singular) and record in COMPUTE-leanfl.
STATUS 00:33: (P4) plan: shared lemmas first. p4c.part: tau_smul, rs_zE, e2_comb, e2b_comb, Ed_comb, Edb_comb, LAG_pair (two independent d1,d2 with Q = 0 and n orthogonal to E(d1),E(d2),E(d1,d2), n chi_1-type => False; normal form + LAG_b), X3c_line, uY_of_rs, DN_line (one-line case: every d in D_N is Q-isotropic and <v,E(d)> = 0). p4d.part: zE2c, chi_t4, DN_pol (polarised), DN_on_z (D_N = C z by LAG_pair), N2_form (N'' = N cap {d = 0} consists of outer(v, x)), P4_Na = branch (N-a) complete (canonical placement: inactive column 4; tau(v^3) = 0 from the cubic, D_N = C z, N'' strongly level 2-dim with only column 4 identically zero vs A1cols). window_files.txt -> FLp.lean (= FLo + p4c p4d, 13094 lines) + Tr10.lean (closure, 4035 lines).
STATUS 00:37: p4e.part: Mv (Gram map of F_v(d) = <v,E(d)>), Mv_ip, Mv_inj (tau v = 0 and all v_k != 0 => F_v nondegenerate; simpler than the paper's character coordinates: no tau(v^3) = 0 needed), Fv_nondeg (no 3-dim F_v-isotropic subspace), three_iso_perp ((c3) part 1: three pairwise independent isotropic lines cannot all be orthogonal to a nonzero E in V). R10 = p4c p4d p4e.
STATUS 00:42: p4f.part: X3c_two, uY_of_rs2, qbar_pol (Qbar polarised: <u_Z,u_Z'> = 2 eps(d_Z,d_Z') on N), Ed_sub, dY_add, dY_sub, P4_Nb_chi = branch (N-b) for a chi_1-type pair (cubic gives the pair relation; (C3') gives F_v = 0 on D_N; Qbar polarisation makes d injective on N, so dim D_N = 3 > 2 >= any F_v-isotropic subspace, Fv_nondeg). Next: (N-b) zero-row pair.
STATUS 00:50: p4g.part (X3c_gen2/3 without tau(v^3) = 0, hvec = 1 - 2 e_{k0} with hvec_sq/ip/tau, tau_single, Mv_hvec (h is in the radical of F_v for a zero-row v), Mv_ker (radical = C h), Edb_self, Edb_comm, pc_hvec (perm[h,h,v,w] = 2<v,w>), dY_inj_two) and p4h.part P4_Nb_zero = branch (N-b) for a zero-row pair: F_v = (tau(v^3)/4) l_v^2 and F_w likewise on N; if h in D_N then l_v(h) = l_w(h) = 0, so zE(h) in K and (Z2) perm[h,h,v,w] = 0 contradicts 2<v,w> != 0; if h notin D_N then F_v(z,.) kills D_N + C h = C^4, so z in C h and h in D_N anyway. Certificates leanfl/gen_nb.py (+ inline). R10 = p4c..p4h; FLp 13823 lines, Tr10 4764 lines, guard 0, no sorry.
STATUS 00:52: p4i.part: rel_two, P4_k2 (one line -> P4_Na; two lines -> pair_rel -> P4_Nb_chi / P4_Nb_zero), P4_k2_conf (realisation of Nbar from dim Nbar = 2), mTC_perm, P4_k2_perm (column-permutation transport, sigma fixing the defect pair), P4_k2_all: in the (P4) configuration, k = 2 active neutral columns is IMPOSSIBLE (all three placements). Remaining (P4): k = 3 branches (c1), (c2-i..iii), (c3).
STATUS 00:53: RESULT ROUND 10 block + handover section 12 written. Next: (c3) part 2 or (c2) groundwork.
STATUS 01:00: (c3) part 2 key fact decided EXACTLY and calibrated (COMPUTE-leanfl.md round 10, leanfl/sing10): no 2-dim strongly level plane with rs = 0, cols 0 = 1 and three pairwise distinct active isotropic lines (all 12 charts unit ideal; type-I plane recognised). P4_c3_Ez (part 1) in p4i.
STATUS 01:04: p4j.part ((c3) part 2: Qbar = 0 on N) written; RESULT ROUND 10 + handover updated. FLp/Tr10 rebuilt (window 3 list unchanged: FLp, Tr10).
STATUS 01:06: p4k.part: uY_of_rs3, indep3, c3_final, TC5_c3 = branch (c3) COMPLETE: E(z) != 0 -> P4_c3_Ez; E(z) = 0 -> c3_Qbar makes {u_Z} totally isotropic (dim <= 1, iso_image) while the kernel of Z -> u_Z on N lies in the zeta part (v_2,v_3,v_4 independent, indep3) -> dim N <= 2 < 3. (Even shorter than the planned Qbar-nondegeneracy route; the exact Singular plane check of COMPUTE r10 is now only a cross-check.) FLp 14287 lines, Tr10 5261.
STATUS 01:06: RESULT ROUND 10 updated ((c3) complete). Preparing report.
STATUS 01:07: ROUND 10 report sent (window 3 not yet run; window_files = FLp.lean, Tr10.lean).

## ROUND 11 (leanfl; start 01:08 UTC). Targets: (1) (c2-i) after exact certification of the DI5.3 (c2) closed forms;
## (2) (c1); (3) (c2-ii,iii) with (F1)/(F2); (4) final TC5 dispatcher; (5) char-p note for verifyfl/verify2 (R11.6).
## NOTE FOR verifyfl / verify2 (char p, R11.6) -- 01:15 UTC
##   The Lean TC5 route (all parts written so far: (P1) TC5_P1, (P2) TC5_P2, (P3) TC5_P3, (P4) TC5_dims/P4_k3, k = 2 P4_k2_all,
##   (c3) TC5_c3, and every FLn lemma they use: LemmaQB/QBc, Lemma Z, TC5 degree conditions, A1/A1b/A1cols, L_slev, LAG) is
##   CHARACTERISTIC-FREE EXCEPT FOR INVERTING 2 AND 3:
##   * every denominator in these parts is 2^a 3^b (2,3,4,6,8,9,12,16,24,32,48,72,96: grep of the closure files Tr8full/Tr9/Tr10);
##   * every integer that must be nonzero has prime factors 2, 3 only (24, 1+c for c in {0,1,2,3}, 3/4, 2<v,w>, ...);
##   * the degree extraction (roots5) uses the nodes 1..5, whose differences 1..4 are units iff char != 2, 3;
##   * no square roots, no algebraic closure, no ordering/analysis: the (P3) pair classification is proved by the y_k = v_k w_k
##     Newton-identity argument (not by the conic parametrisation with I and sqrt 3), (c3) by isotropy/dimension counting.
##   So, once (c1) and (c2) are added in the same style, the proof should hold over ANY field of characteristic != 2, 3
##   (the Lean text is over C; porting = replacing C by a field F with (2 : F) != 0, (3 : F) != 0). Caveats: (c1)/(c2) not yet
##   written; the closure tool lists s1.part's r3 (uses Complex.I) only because of a variable-name collision, not a real dependency.
STATUS 01:19: (c2-i) written: p5a.part (c2_X3c5/3/4 = the certified closed forms of Tbar_5, Tbar_3, Tbar_4; generated, certificates by leanfl/gen_c2.py), p5b.part (c2_rels: (C3') and Tbar_1 = 0 in closed form at any Z in N; chi_t12: for chi_1-type v and isotropic w in V, tau(v w^2) = 0 => tau(v^2 w) = 0), p5c.part P4_c2i (canonical placement lines (v,v,w) on columns 2,3,4; (c2-i) parametrised by l3 - l4 = lam (l3+l4) + mu b: t3 = 0, then t12 = t21 = 0, F_v = 0 on N, d injective (qbar_pol), dim D_N = 3 > 2 (Fv_nondeg)). All certificates sympy-checked. Build: R11 = p5a p5b p5c -> lean/fl/FLq.lean, leanfl/Tr11.lean.
STATUS 01:22: (c2-ii) written: p5d.part P4_c2ii (Nbar = {l3 + l4 = c b}, c != 0: t3 = 0, then t21 = t12 = 0, pair_rel => chi pair, the u-bracket = (3/16) c^2 <v,w>^2 != 0 at one point; certificate leanfl/gen_c2ii.py). Next: (c2) plane analysis (coefficient map, P = ker p) -> dispatch to (c2-i)/(c2-ii)/(c2-iii).
STATUS 01:27: p5e.part (coefL, coefL_vals, c2_plane: in a (c2) configuration N's coefficient vectors (l3,l4,b) span a 2-dim space with explicit generators), p5f.part (smul_v_inj, cramer, P4_c2_canon: (c2) canonical dispatcher -> P4_c2i (det != 0, lam/mu by Cramer) / P4_c2ii (a = c b, c != 0) / hypothesis for (c2-iii) (a = 0)).
STATUS 01:28: coordinator re-prioritised: TOP target = port FLk (Lemma SL, Theorem FL) + TC5 blocks from C to a field K with i^2 = -1 and (N : K) != 0 hypotheses. (P4) piece finished first: P4_c2_canon (p5f) complete in source; remaining (P4): (c1), (c2-iii), transport + TC5 dispatcher (not started). Switching to the port.
STATUS 01:52: field port v1 built: lean/fl/FLK_field.lean (7748 lines; generated by leanfl/port.py + port_header.txt + port_patches.json from the FLk parts into lean/fl/K/*.part; buildK.sh). Hypotheses: NeZero (2,3,5,7 : Kf), Fact (exists i, i^2 = -1), Fact (every set of <= 20 elements misses a point; generic_pt needs it, Infinite in FLk). window_files.txt: FLK_field first, then FLq (supersedes FLp), then Tr11.
STATUS 01:58: RESULT ROUND 11 written at the top. TrK11.lean (TC5 parts over Kf) built and queued 2nd in window_files.
STATUS 02:01: handover section 13 written.
STATUS 02:02: final port build: FLK_field.lean 8006 lines, TrK11.lean 7531 lines (both guard 0); window_files.txt = FLK_field, TrK11, FLq, Tr11. No compile run by me (windows only).
STATUS 02:03: round 11 handing back (window 3 not started; its logs go to the next round).
STATUS 02:04: added leanfl/TrK0.lean (smoke test, 1468 lines) first in window_files; buildK.sh rebuilds it.

# ROUND 12 (start 02:06 UTC). Targets: (1) window-3 repairs of the field port (porter/header/patches, buildK.sh), note silent char-0 simp/norm_num; (2) (c2-iii) via (F1)/(F2)/G23, and (c1); (3) final TC5 dispatcher (TC5 over Kf as one theorem).
STATUS 02:06: round 12 started; window 3 expected ~02:30-04:00 (TrK0, FLK_field, TrK11, FLq, Tr11). Working on (c2-iii) while waiting.
STATUS 02:12: p5g.part (C1Hyp, C2iiiHyp as Prop hypotheses; P4_c2_perm transport; TC5_main: DefLine K mTC -> finrank K <= 4, given C1Hyp and C2iiiHyp) added to R11; FLq (15083 lines) and Tr11 rebuilt atomically. Porter fix: binder shadowing now detected in every signature group (rel_prop/no_triangle have a local r3) and shadowed names no longer pull a declaration into the i-closure: the TC5 parts (rounds 8-11) do NOT need i^2 = -1 (they need |Kf| > 20 via A1/generic_pt blocks). TrK11 regenerated (7680 lines) -- the old TrK11 had (r3 (Kf := Kf)) inserted into rel_prop's binder; FLK_field unchanged.
STATUS 02:19: p5h.part: indep_of_np, sig23, c2iii_zeta ((c2-iii) with a realisation (l, -l, b), l b != 0, whose d lies in C z is impossible: subtract c zE(z), the element (-b w/2, -b w/2, l v, -l v, b w) spans a strongly level line (L_slev) and pattern23 (G23) kills it -- covers the paper's sub-case D_N = zeta), C2iiiLagHyp (the remaining Lagrangian sub-case as hypothesis), C2iii_of_lag, TC5_main' (TC5 from C1Hyp + C2iiiLagHyp). FLq 15207, Tr11 6555, TrK11 7943 lines rebuilt.
STATUS 02:25: (F1) formalised: p5i.part (F1_vprod, F1_w0..3, F1_zero_row; Singular lift certificates, sympy-checked, integral) and p5j.part (c2iii_zero_row: in (c2-iii) t3 v v w = 0, 3 t4 v v w w = <v,w>^2 and v, w share a zero coordinate). FLq 15271, TrK11 8013 lines. TrK0 still compiling (57 KB log, no errors so far).
STATUS 02:29: waiting for window 3 (TrK0 compiling since 02:05; the log is block-buffered by the grep pipe, so its size says nothing about progress). Handover section 14 written.
STATUS 02:38: plan for the (c2-iii) Lagrangian sub-case (all steps checked on paper; algebra checked in Singular where noted):
  1. c2iii_zero_row: v k0 = w k0 = 0 (done, p5j).
  2. u := Ed z: tau u = 2 e2 z = 0 (tau_Ed, LemmaZ), <v,u> = <w,u> = 0 (LemmaZ on the realisation (1,-1,1)).
  3. u is constant off k0: Singular sing12/s3.sing: g^2 (u_a - u_b) in (v_k0, w_k0, tau v, tau w, <v,v>, <w,w>, <v,u>, <w,u>, tau u)
     for a, b != k0 (lift + sympy as for F1; generate the four k0 frames by relabelling).
  4. (F2) by hand: with T = tau z, z_m^2 - T z_m = lam (m != k0), z_k0^2 - T z_k0 = -3 lam: pairwise (z_a - z_b)(z_a + z_b - T) = 0
     and the 8-way split give z = T e_i (some i) or z = (T/2) hvec k0; z != 0 forces T != 0.
  5. z = (T/2) hvec k0: LemmaZ's pc z z (col 2) (col 4) = 0 at (1,-1,1) and pc_hvec give (T^2/2) <v,w> = 0. Contradiction.
  6. z = T e_i: d = dY Z11 is not in C z (C2iiiLagHyp premise), z0 := d - (tau d / T) z in D_N has tau z0 = 0, e2 z0 = 0 (qbar_pol:
     uY Z = -(b/2) w is isotropic), z0_i = 0 (LemmaZ e2b (dY Y) z = 0), Edb z0 z = -(T/2) z0, so perp_line gives <v,z0> = <w,z0> = 0;
     three_iso_perp (E := z0; a, b, c := v, w, z0) or z0 parallel to v or w (then <w,z0> = s g = 0) gives the contradiction.
  Generator per k0 frame (4 copies) is the intended Lean route; ~300 lines. Next round.
STATUS 02:42: window 3: TrK0 1720 s, 2 errors (Vp_finrank: (X (Kf := Kf)) (n := 4) syntax; fixed in port.py: no outer parentheses before a named argument). FLK_field/TrK11 stopped by the coordinator (too slow, ~50 lines/min). Speed: field now runs with a cheap discharger (first | assumption | simp only [nz..]); TrK0p.lean = profiled smoke test; SL split into FLK_SLa..d (closures of SL_of, HypS6, HypS7, HypS8) + FLK_FL. window_files.txt = Stage A (TrK0p, FLK_FL).
STATUS 02:45: p5k.part (uconst_0..3: step 3 of the Lagrangian plan, Singular lift certificates relabelled per frame, sympy-checked, scaled by 2) and p5l.part (F2_scalar: the (F2) classification as a scalar lemma, every step sympy-checked by leanfl/chk_f2.py) added; FLq 15352, Tr11 6700, TrK11 8099 lines. Stage A (TrK0p, FLK_FL) booked by the coordinator after window 3.
STATUS 02:51: p5m.part: pc_smul2, c2iii_h (sub-case z = (T/2) hvec k0: pc z z v w = T^2 <v,w>/2 = 0 forces T = 0), c2iii_ei (sub-case z = T e_i: z0 = T d - tau(d) z spans D_N cap V, z0_i = 0, Edb z0 z = -(T/2) z0, perp_line gives <v,z0> = <w,z0> = 0, qbar_pol gives z0 isotropic, three_iso_perp). Steps 5-6 of the Lagrangian plan are in source; only the frame wrapper (uconst_k0 + F2_scalar + case dispatch) remains for (c2-iii). FLq 15483 lines (window 3 compiles the 02:35 copy = prefix up to p5j).
STATUS 02:54: p5n.part: c2iii_core (generic frame k0 | a b c: uconst result + F2_scalar + dispatch to c2iii_ei / c2iii_h), C2iiiLag_proof : C2iiiLagHyp (fin_cases on the zero-row index, frame facts by simp/decide, uconst_k0 cancelled by 2 <v,w>^2), TC5_of_c1 : C1Hyp -> DefLine K mTC -> finrank K <= 4. So (c2-iii) is closed in source; TC5 now rests on C1Hyp only (pending compile). FLq 15612, Tr11 6964, TrK11 8368 lines.
STATUS 02:56: FLq (window 3, partial log): 3 errors so far, all fixed in the C parts: finrank_range_le_card needs (R := C) in TC5_P3 (p3c) and P4_k2_conf (p4i) [stuck instance when used in a bare have]; chi_t12 (p5b) e21 closed by simp only -> now rfl. Rebuilt FLq/Tr11/TrK11 (and FLK_field with the new porter).
STATUS 02:56: (c1) plan for next round: split on t3 v v v. If t3 v v v = 0: DN_line (p4c) gives e2 d = 0 and <v,E(d)> = 0 on D_N, LAG_pair forces D_N = C z, so N'' = N cap {d = 0} is a 2-dim strongly level outer(v, .) space with all three neutral columns active -- compare with P4_Na (round 10), which used A1cols on the same kind of space. If t3 v v v != 0: the paper's Lambda345 / S8-type run / 'sigma has no line' argument (needs reading DI5.3 (c1) again).
STATUS 02:59: FLq (window 3, 02:35 copy = parts up to p5j): exit 1, 1384 s, 5.95 GB, 17 errors in 7 declarations, ALL fixed in source now: TC5_P3 (p3c) and P4_k2_conf (p4i): finrank_range_le_card in a bare have needs (R := C); chi_t12 (p5b): simp only closed the goal (now rfl); P4_c2_canon (p5f): hcomb arguments lost their parentheses (generator f-string) and congr 1 already closed the e4 goal (now rw [e4, F1] / rw [e4, Fb]); sig23 / c2iii_zeta (p5h): Equiv.swap 0 2 * Equiv.swap 1 3 applied to a numeral has no known type (now def sig23p : Equiv.Perm (Fin 5)); F1_vprod (p5i): maximum recursion depth (now set_option maxRecDepth 20000 in). Everything else compiled, including rounds 9-11: TC5 (P1)-(P3) blocks, the k=2 cases P4_Na/P4_Nb_chi/P4_Nb_zero/P4_k2_all, P4_k3, TC5_c3, c2_rels, P4_c2i, P4_c2ii, c2_plane, P4_c2_perm, TC5_main, F1_w0..3, F1_zero_row, c2iii_zero_row. (p5k-p5n were not in that copy.) C rate: 11 lines/s vs the port's 0.85.
STATUS 03:00: FLq has 19 errors (I first counted 17): plus cramer (p5f) used div_add_div_same, which is not in this Mathlib -> now rw [..., ← add_div, ...]. All 19 fixed; FLq/Tr11/TrK11 rebuilt.

# ROUND 13 (start 03:01 UTC). Targets: (1) (c1) (t3 v v v = 0 vs != 0) so TC5 is unconditional; (2) speed fix from TrK0p's profile; (3) keep FLq/TrK11 rebuilt.
STATUS 03:01: round 13 started.
STATUS 03:10: (c1) progress (source): p5o noline (the cubic (l3+l4)(l4+l5)(l5+l3) - l3 l4 l5 contains no line: 4 m^4 in the ideal for every 2x2 minor, INTEGRAL certificates from Singular over Z (the rational lift had 7 in denominators; char-7 check shows 7 is not needed), sympy-checked); p5p c1_plane (coefficient plane, adapted from c2_plane); p5q c1_eqs, c1_reduce (t3 v v v != 0 is impossible via noline; t3 v v v = 0 forces the plane to be Lambda345 via generic_t and the quartic; realisations by Cramer), C1chiHyp, C1_of_chi, TC5_of_c1chi; p5r C1RHyp, C1chi_of_R (DN_line + DN_on_z: D_N in C z, so R = v (x) Lambda345 with zero columns 0,1 lies in K), TC5_of_c1R. Remaining: the paper's S8 run (elements of K outside N) for C1RHyp. FLq 16k, TrK11 ~8.8k lines rebuilt.
STATUS 03:11: C1RHyp (the only open TC5 hypothesis) = paper's 'S8 run' in (c1): needs elements of K outside N. Available tools: TC5_deg_i (X2c/X3c/pc of (uY, y2, y3, y4) vanish for every Y in K), TC5_degree (deletions), NB_qbar + neutral_pol (C2 and C2pol: b_j := 2 y_j - rs Y has <b_j,b_j> = <n,n> and <b_j, z_j> = 0 for Z in N, so b_j is orthogonal to v), NB_plane (S nondegenerate => N's neutral columns vanish, so here S = rs(K) is degenerate). Plan: (i) apply TC5_deg_i to Y + s R_ab (R = v (x) Lambda345, cols 0,1 zero) as polynomial identities in s, a, b; the X3c coefficient gives <v^2, n> = 0 for n = rs Y (paper: Tbar_1 => n0 in C chi1 or C chi3); (ii) S is a degenerate 2-dim subspace of V containing an isotropic u with S = u^perp; with (i) S = span(v, v^2)?? -- to be settled; (iii) the two sub-cases n0 = c v^3 / c v via the u-deletion bracket (TC5_degree pc part) and the fourth vector. Needs a fresh round.
STATUS 03:12: S8-run plan for C1RHyp made concrete (checked by hand):
  (a) S = rs(K) is 2-dim (TC5_dims) and DEGENERATE: otherwise NB_plane kills the neutral columns of N (contradicts activity). So
      there is n0 != 0 in S orthogonal to S, hence isotropic, and Y0 in K with rs Y0 = n0.
  (b) For Y in K and the R-elements (0,0,a v,b v,-(a+b) v): TC5_deg_i X2c part, linear in s, gives <v,y2> = <v,y3> = <v,y4> =: sigma;
      NB_qbar + neutral_pol give b_j := 2 y_j - n orthogonal to v, tau b_j = 0, <b_j,b_j> = <n,n>; for Y = Y0 (n0 isotropic) b_j is an
      isotropic vector of v^perp cap V, so b_j = beta_j v (the (Q4) fact; Lean has iso_quad / perp lemmas).
  (c) X3c part, s^2 coefficient: (1/2) e2(l) <v^2, n0> = 0 (uses t3 v v v = 0, <v^2,v> = 0, u = (-n0 - sum b_j)/4), so <v^2,n0> = 0
      and n0 lies in span(v, v^3) cap {isotropic} = C v u C v^3 (<v,v^3> = 4 kappa != 0).
  (d) n0 = c v^3: the u-deletion bracket (TC5_degree pc part on Y0 + s R) has an x3x4x5 coefficient 6 t (sum beta) and then an
      x-quadratic part -t^2 c^2 e2(x) != 0.  n0 = c v: bracket -24 p_u p3 p4 p5 forces u(n0) = 0, so v (x) C^{345} lies in K
      (3-dim R), and the fourth vector (rs = v^2 + pi v) gives the final -24 t^4 != 0 (paper text, NOTES-verifyfl DI5.3 (c1)).
  Each step is a polynomial identity in s, a, b and the entries; certificates by sympy as for (c2). Next round.
STATUS 03:15: Tr11 (window 3, 02:58 copy): 20 errors = the FLq ones (same declarations) plus two NEW kinds, now fixed: (1) with finrank_range_le_card elaborated, omega cannot identify Set.finrank C (range b) with finrank C (span C (range b)) in TC5_P3 (p3c) and P4_k2_conf (p4i) -> simp only [Fintype.card_fin, Set.finrank] at h3/h2; (2) C2iiiLag_proof frame k0 = 3 (p5n): simp only [tau]/[ip] already closes tau x = x 0 + x 1 + x 2 + x 3, so ring had no goal -> (fun x => rfl) (fun x y => rfl). FLq/Tr11/TrK11 rebuilt.
STATUS 03:18: S8-run groundwork for C1RHyp (source): p5s exists_iso_rs (step (a): an active neutral column forces rs(K) degenerate via NB_plane, giving Y0 in K with rs Y0 != 0 isotropic); p5t uY_R, c1R_ipv, c1R_cols (step (b): X2c cross terms give <v,y2> = <v,y3> = <v,y4>, sympy-checked certificate); p5u c1R_half (step (b): 2<v,y_j> = <v, rs Y> via NB_qbar + neutral_pol). Next: X3c s^2 coefficient (step (c)) and the two sub-cases (d).
STATUS 03:22: p5v c1R_x3c (X3c s^2 coefficient for Y +- R_ab, certificate by gen_s8c.py: tau/ip multipliers found by elimination, full identity sympy-checked); p5w c1R_b (b_j = 2 y_j - n0 is a multiple of v by Q4) and c1R_v2n (step (c): t3 v v n0 = 0 for isotropic n0 = rs Y0; certificate sympy-checked). With vperp_coords this gives n0 = p v + r v^3, p r = 0. Remaining for C1RHyp: sub-cases n0 = r v^3 and n0 = p v (step (d)).
STATUS 03:24: (c1) step (d), computed in the Qv calculus (vectors x = Qv v 0 x1 0 x3, ip = 4 kappa (x1 y3 + x3 y1),
  t4 = 4 kappa prod(x1) + 4 kappa^2 (sum over 2 of the 4 taking x3) + 4 kappa^3 prod(x3), pc = br for tau = 0 vectors via pc_full):
  * n0 = r v^3: y_j = Qv v 0 (beta_j/2) 0 (r/2), u = Qv v 0 (-sum beta/4) 0 (-r/4). The quartic f(s) = pc(u, y2 + s a v, y3 + s b v,
    y4 - s(a+b) v) (TC5_deg_i at Y0 + s Z, s = 0, +-1, 2) has s^3 coefficient -6 a b (a+b) kappa (sum beta) and s^2 coefficient whose
    a^2 part is kappa (kappa r^2 - 3 beta_3 sum beta). So sum beta = 0 (a = b = 1), then kappa^2 r^2 = 0 (a = 1, b = 0): r = 0,
    contradicting n0 != 0. SHORT, all polynomial.
  * n0 = p v: all columns of Y0 are multiples of v and f(s) = -24 kappa (u-coef) prod_j(c_j + s l_j), so u-coef = 0, i.e. u = 0;
    then v (x) C^{345} lies in K up to zeta, and the paper's fourth-vector argument (rs Y4 not in C v) finishes. Longer.
STATUS 03:29: p5x pc_Qv13 (pc of four Qv v 0 x 0 y vectors for a chi line: -24 kap prod x1 + 8 kap^2 (pairs) - 24 kap^3 prod x3; generated + sympy-checked by gen_pcqv.py) and p5y c1R_case_v3 (sub-case n0 = r v^3 => r = 0: quartic at Y0 + s Z, s = 0, +-1, 2, Z = R(1,1) and R(1,0); 6 f3 = -72 kap sum(beta), 2 f2 = 2 kap (kap r^2 - 3 beta3 sum(beta))). Remaining for C1RHyp: sub-case n0 = p v (fourth vector).
STATUS 03:30: sub-case n0 = p v plan (Qv calculus): all columns of Y0 are multiples of v, quartic = -24 kap c0 prod(c_j + s l_j), so
  c0 = 0, i.e. u(Y0) = 0 and p + sum beta = 0; S = rs(K) = span(v, v^2) (S is in n0^perp = v^perp cap V); take Y4 with rs Y4 = v^2 + pi v;
  its columns y_j = pi_j v + kap_j v^2 (vperp1_coords + c1R_half-type C2pol with R and Y0), NB_qbar gives kap_j^2 = kap_j; then X3c
  (Tbar_1) at Y4 + x-combinations of {R, Y0} gives kap_j = -kap_u, 2 kap_u + sum kap_j = 1 => kap_j = 1, kap_u = -1, then pi_u = 0,
  and the quartic pc(-t v^2, x3 v + t v^2, x4 v + t v^2, x5 v + t v^2) = -24 t^4 kap^? != 0. All via pc_Qv13 / ip_Qv. Next round.
STATUS 03:31: p5z c1R_case_v_u (sub-case n0 = p v, first step: uY Y0 = 0 and Y0's neutral columns are c_j v with c2 + c3 + c4 = p; 6 f3 = -72 kap (p + sum beta), sympy-checked). Remaining for C1RHyp: the fourth-vector part of n0 = p v, then the assembly (vperp_coords split n0 = p v + r v^3, p r = 0).
STATUS 03:32: fourth-vector part of n0 = p v, precise plan (checked by hand in the Qv calculus):
  (a) strengthen exists_iso_rs: n0 is in the radical of S = rs(K) (n0 = B a - A b is orthogonal to a and b; S = span(a,b) by finrank);
      so <v, n> = 0 for n in S. (b) some Y4 has rs Y4 not in C v (finrank S = 2); vperp1_coords and scaling: rs Y4 = Qv v 0 pi 1 0.
  (c) Y4's columns y_j = Qv v 0 pi_j kap_j 0 and uY Y4 = Qv v 0 pi_u kap_u 0 (c1R_half gives <v,y_j> = 0), 2 kap_u + sum kap_j = 1,
      NB_qbar gives kap_j^2 = kap_j. (d) W_x in K with uY W = 0, cols x_j v for every x (W = (sum x / p) Y0 + R_l). X3c(Y4 + W_x) is
      quadratic in x (t3 v v v = 0) with x_a x_b coefficient 8 kap (kap_u + kap_c) ({a,b,c} = {2,3,4}); so kap_j = -kap_u, hence
      kap_u = -1, kap_j = 1. (f) x_j = -pi_j: pc(Qv v 0 pi_u (-1) 0, v^2, v^2, v^2) = 24 kap^2 prod(b) - 24 kap prod(a) = -24 kap^2 != 0,
      contradicting TC5_deg_i's pc component. Needs a pc_Qv12 lemma (Qv v 0 a b 0 vectors: pc = 24 kap^2 prod b - 24 kap prod a)
      and the t3/X3c analogue (t3 = 4 kap (a1 b1 c2 + a1 b2 c1 + a2 b1 c1)), generated like pc_Qv13.
STATUS 03:33: p5aa pc_Qv12 (pc of Qv v 0 a b 0 vectors = 24 kap^2 prod b - 24 kap prod a) and x3c_Qv12 (X3c of four such vectors), generated + sympy-checked by gen_qv12.py: the tools for the fourth-vector step.
STATUS 03:34: p5ab exists_rad_rs (n0 = rs Y0 != 0 in the RADICAL of S = rs(K): <n0, rs Y> = 0 for all Y in K).
STATUS 03:39: (c1) CLOSED IN SOURCE: p5ac c1R_W (W_x in K with uY = 0 and columns x_j v, from Y0 and R) and c1R_case_v_final (fourth vector Y4: rs Y4 = Qv v 0 pi q 0, q != 0; columns Qv v 0 pi_j kap_j 0; 2 kap_u + sum kap_j = q; X3c at Y4 + W_x gives kap_u + kap_j = 0 (x_a x_b coefficients, sympy-checked); so kap_u = -q, kap_j = q; pc at x = -pi gives 24 kap^2 q^4 = 0, contradiction); p5ad C1R_proof : C1RHyp (exists_rad_rs, c1R_v2n, vperp_coords split p r = 0: r-case by c1R_case_v3, p-case by c1R_case_v_u + c1R_case_v_final) and TC5_final : DefLine K mTC -> finrank K <= 4 -- TC5 UNCONDITIONAL in source (pending the FLq/TrK11 compiles). New parts use only the denominators 2, 4 and the numerals 3, 4, 8, 24, 72: still (2,3 : Kf) != 0 for the TC5 parts themselves. FLq 16657, Tr11 8049, TrK11 9479 lines.
STATUS 03:42: waiting for Stage A (window 3 is on leanzbf's R12s_combo since 03:28). Files for the FLq rebuild are final: lean/fl/FLq.lean (16657 lines, includes TC5_final); TrK11.lean (9479 lines) for Stage B.
STATUS 03:46: porter: field discharger now 'simp only [nzs]' with one conjunction lemma nzs (all numeral facts) instead of a 33-name list at every fallback site: files shrink (FLK_field 515 -> 420 KB, TrK11 857 -> 704 KB, TrK0p 75 KB) -- less syntax for parser and linters. TrK0p (not yet started) regenerated atomically with this change.
STATUS 03:56: handing back round 13. Stage A has not started (window 3 still on leanzbf's ZBF file), so the speed fix waits for TrK0p's profile next round. Queue (window_files.txt): TrK0p (regenerated with the nzs discharger), FLK_FL, FLq (C rebuild incl. TC5_final); Stage B after the speed fix.

# ROUND 14 (start 03:57 UTC). Targets: (1) speed fix from TrK0p's profile, revised Stage B timeouts; (2) repair the FLq rebuild; (3) book Stage B; (4) optional Tr13.
STATUS 03:57: round 14 started; waiting for TrK0p_port.log (after window 3, ~04:28).
STATUS 03:58: TrK0p (profiled, nzs version) started compiling at 03:58 UTC.
STATUS 04:00: prepared an A/B porter switch PORT_NOSIMP=1 (numeral lemmas without @[simp]; bare norm_num calls get [nzs, zns, nes]; header proofs untouched), for use if the profile blames the global numeral simp lemmas. Main build unchanged.
STATUS 04:13: TrK0p (nzs version): 729 s, 42 errors -- simp only [nzs] cannot close (N : Kf) != 0 without ne_eq, so field_simp kept the numeral denominators. Fixed: disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]. Profile (cumulative): simp 45 s, typeclass inference 44 s, ring 21 s, field/field_simp ~23 s, elaboration 22 s; hot spots are the pc-expanding decide-simps (same cost as over C). Built TrC0p (same blocks over C, profiled) as baseline. Requested: TrK0p rerun, TrC0p, then Stage B (SLa 60, SLb/c/d 45, TrK11 150 min).
STATUS 05:15: resumed after the account cut-off (~04:25). Coordinator: FLq rebuild = 7 errors, ALL heartbeat timeouts (200000), at FLq lines 14882/14889/14898 (P4_c2_canon), 15184 (F1_vprod), 15606 x2/15609 (noline); everything else compiles (0 sorry). Cause: per-declaration heartbeat budget eaten by the big linear_combination certificates; the later cheap steps (norm_num, rw) then time out. FLK_FL (old discharger): 1 error, propR (case a goal with 120/5 and (5+0)/5 left, i.e. (5 : Kf) != 0 not discharged).
STATUS 05:18: fix in the parts: set_option maxHeartbeats 4000000 in before P4_c2_canon (p5f), F1_vprod (p5i), noline (p5o); backups in leanfl/bak14/. lean/fl/FLq2.lean = FLq parts with the fix (md5 11b60a129a, 16660 lines, diff vs FLq.lean = exactly these 3 lines); FLq.lean kept unchanged (7a1f2e7aca). Booked by the coordinator as LEANFLQ2 (50 min, log leanfl/FLq2.log, leancompile third argument prints axioms of TC5_final too). Do not touch FLq2.lean before its run.
STATUS 05:22: buildK.sh rerun: only TrK11 changed (d34ad9249a, 9485 lines; the three declarations now carry 16000000 = 4 x 4000000 by the porter rule); FLK_SLa..d, FLK_FL (0d7f568f89, new discharger), TrK0/TrK0p unchanged. Tr11 (82f261fdf9, 8052) and Tr13 (52065b9244, 8066) regenerated by hand from build8.sh's closure lines (build8.sh itself NOT run, it would overwrite FLq.lean). Waiting for TrK0p2 (rerun with the new discharger; contains propR) to confirm FLK_FL.
STATUS 07:08: TrK0p RERUN (new discharger): 0 errors, 0 sorry, 160 s (was 1720 s with the 33-name list, 729 s/42 errors with bare nzs), peak 7.7 GB. SPEED FIXED: the failing (N : Kf) != 0 discharger made field/field_simp expensive at every fallback site; now ~0.11 s/line = the C rate (FLq 0.10 s/line). Profile: simp 33 s (pc-expanding simps, as over C), field 10 s, ring 6 s, typeclass 0.7 s. propR (in TrK0) passes -> FLK_FL's 552:84 error fixed. Proposed Stage B: FLK_field.lean (whole SL+FL port + C corollary, ab5e1e4d26, 8012 lines) as ONE job (45 min), TrK11 (d34ad9249a, 60 min); split SL files only as fallback. FLq2 (LEANFLQ2) compiling since 07:06.
STATUS 07:09: Stage B BOOKED by the coordinator: LEANFLK_FIELD (FLK_field.lean ab5e1e4d26, 45 min, log leanfl/FLK_field_x.log), then LEANTRK11 (TrK11.lean d34ad9249a, 60 min, log leanfl/TrK11_x.log), after FLq2/R14t_shape/R17lint (~08:30-10:30 UTC). FLK_FL and FLK_SLa..d unbooked fallbacks. PEqualNP.Defs rebuilt 07:06 (additive upstream modules). Waiting for FLq2.log (both axiom lines).
STATUS 07:31: FLq2 (LEANFLQ2): exit 0, 0 errors, 0 sorry, 1418 s, peak 8.95 GB; axioms of L_gct_210 and TC5_final = [propext, Classical.choice, Quot.sound]. TC5 compiled over C. Handing back round 14.
## CERTIFICATE PIPELINE (round 15, leanfl; data in leanfl/cert/)
Question: can the Groebner UNIT verdicts (mostly mod P1 = 2147483629 under the whole-cover RED-p rule) be checked in Lean
without native_decide, and at what cost?
(A) RED-p IN LEAN -- DONE as a core (LEANTCERT, leanfl/cert/Tcert.lean, 0 errors on the first compile):
  * redp_valsub: for a prime p there is a ValuationSubring B of C with (p : C) in B.nonunits (Mathlib
    Ideal.image_subset_nonunits_valuationSubring applied to I = (p) in the subring bot = image of Z). This replaces "reduce a
    number-field point at a prime above p": no number fields, no algebraic closure, no properness theory is needed.
  * proj_norm: z != 0 in C^n -> some k with z k != 0 and all z i / z k in B (take the coordinate of largest valuation).
  * unit_contra: 1 = p * g in B is impossible.
  * Use: a chart certificate is a polynomial identity over Z, 1 = sum c_j f_j + p * G, stated for an ARBITRARY CommRing R and checked
    by linear_combination; applied in R = B it gives 1 in pB, contradiction. So: closed projective system with a complex point ->
    normalised point with coordinates in B -> some chart's equations hold in B -> contradiction. Only identities over Z are checked.
  * Still to formalise (one-time, estimate 200-400 lines): the Grassmannian version of proj_norm (choose the k x k minor of largest
    valuation; Cramer => the chart coordinates are ratios of minors, so they lie in B), and the residue field B/m (CharP p) for families
    whose case split is done IN characteristic p (R7.1: F2_p, isotropic lines ...). Those case splits must then be formalised over a
    generic field, exactly as the Kf port did for SL/FL/TC5 (now at the C speed).
  * Q-certificates (Singular over Q) avoid RED-p entirely: CC34 chart 0123 has 12 = sum c_j f_j with integral c_j (only 2, 3 in the
    denominators), valid in every characteristic != 2, 3.
(B) LEAN COST PER CERTIFICATE (Tcert profile, net of the Mathlib import of ~4.5 min per file):
  CC34 chart 0123, 570 cofactor terms, ~7000 term products: 19 s (Q version), 21 s (mod-P1 version with the explicit G, 237 terms);
  i.e. ~3 ms per product (ring 4-5 s, share common exprs 4 s, elaboration 3.5-5 s, type checking 3.4-4 s, linting 1.4 s).
  Scaling test LEANTCERT2 (queued, ~09:30-10:00): 116, 810, 7753, 36290, 88123 products; LEANTCERT3: 727130 products.
(C) CERTIFICATE GENERATION -- THE REAL BOTTLENECK. Singular lift (cofactors) is far harder than msolve's unit verdict:
  * DC3 m12m3 at P1 (252 cases: 81 constant-equation, 171 msolve UNIT, 133 of them < 0.05 s, 38 >= 0.05 s, 10 >= 0.3 s).
    30 sampled UNIT charts, Singular lift mod P1 with 60 s / 0.5 GB each:
    - 20 random charts (msolve <= 0.08 s): all lift in <= 0.2 s; cofactor terms median ~54, max 2658, degree <= 6.
    - 10 hardest (msolve 0.3-4.9 s): 1 lifts (msolve 0.3 s: 25.8 s, 25943 terms, 727130 products), 9 FAIL (60 s / 0.5 GB).
  * Others: stage3 fc_FULL_00001 3627 terms (0.5 s); vf A2 chart13 26 terms (unit by a degree-1 combination); IV2 chart 012 34 terms
    of degree 0; PT2 chart 01_01_01: msolve 21 s, Singular std alone > 300 s at 0.5 GB (no lift).
  * So ~85-90% of charts give small certificates (seconds in Lean), and the msolve-hard tail (>= ~0.3 s, roughly 5-10%) gives
    no certificate with Singular lift in small memory, or huge ones (10^4-10^5 terms, 10^5-10^6 products = minutes-hours in Lean
    at 3 ms per product if linear).
(D) VOLUME: the project has ~5000 UNIT result files (with re-runs and cross-checks) and the manifests list 1674 UNIT +
  833 constant-equation charts; the proof needs O(10^3) distinct non-trivial UNIT charts. msolve times of the 1674 manifest UNIT
  charts: median 0.02 s, p90 0.18 s, p99 14 s, max 474 s; 525 take >= 0.05 s and 128 (7.6%) take >= 0.3 s (the hard tail). At a median of ~5-20 s per chart
  that is roughly 3-15 h of Lean elaboration -- possible only split over several files (or the single-file final made
  very long), plus the hard tail.
(E) ALTERNATIVES for the tail and for speed:
  1. Staged certificates = the R7.2 subsystem cut in Lean: certify each GB(S1) element by its own (small) lift, add it as a
     have, then the final unit certificate is small. This is the same staging that makes msolve fast; most promising.
  2. Linear elimination first (many charts have 10-40 linear equations): substitute, then lift the smaller system.
  3. Trace certificates (GB elements with reduction traces, each step a short linear_combination): best sizes, but no
     installed tool emits traces (Singular/msolve do not; no M2/Sage/CoCoA here); needs a traced F4 implementation.
  4. Reflection: a verified sparse-polynomial checker evaluated by the kernel (decide +kernel / rfl, no native_decide),
     certificate data as Nat literals (strings are banned). One-time cost ~1-3 weeks; expected 10-100x faster per product than
     ring; would make the 10^5-10^6-product certificates affordable.
  5. Big-slot lift (6 GB, 30 min) for the hard tail; Singular modular lift (modStd-style) not tested yet.
(F) VERDICT (scoping): a complete Lean proof is a MONTHS-scale job, not weeks. The RED-p logic is cheap (core done) and the chart
  certificates for ~90% of charts are automatic; the dominant costs are (i) formalising each family's generator (statement ->
  chart equations, plus the char-p case split over a generic field), ~25-40 families at roughly 1-3 days each, and (ii) the
  msolve-hard tail, which needs staged or traced certificates (or reflection) instead of plain Singular lift.

# ROUND 15 (start 07:31 UTC). Targets: (1) Stage B logs; (2) certificate pipeline scoping (Nullstellensatz certificates in Lean, RED-p step, size/time per chart); (3) copy upstream L_gct_152 if cheap.
STATUS 07:40: target 2 started. CC34 chart 0123 (verify2 r18, 16 vars, 10 linear + 20 cubic): Singular lift over Q (12 = sum c_j f_j, 570 cofactor terms, deg 2, denominators only 2, 3) and mod P1 (570 terms; G = (1 - sum)/P1 has 237 terms). Lean test leanfl/cert/Tcert.lean (RED-p core via Mathlib's Ideal.image_subset_nonunits_valuationSubring + both chart certificates) sent for a small compile. Lift sweep on 5 real P1 charts running (pt2 chart already > 3 min in Singular lift, msolve < 1 s).
STATUS 07:48: LEANTCERT (leanfl/cert/Tcert.lean) compiled: 0 errors, 335 s (import ~4.5 min). RED-p core (redp_valsub, proj_norm, unit_contra) + CC34 chart 0123 certificates (Q: 12 = sum c_j f_j; P1: 1 = sum c_j f_j + P1 G) + their chart-level use in B. ~20 s per 570-term certificate (~3 ms per term product). Tcert2 (116..88123 products) and Tcert3 (727130) queued for the cost curve.
STATUS 07:55: DC3 m12m3 lift sample (30 charts, 60 s / 0.5 GB): 20 random charts all lift in <= 0.2 s (median 54 cofactor terms, max 2658); of the 10 msolve-hardest, 1 lifts (25943 terms, 25.8 s), 9 fail. elimpart (linear elimination) before lift on rho1_piv01_l0_ab_ab: still out of memory. CERTIFICATE PIPELINE section written (above the round-15 header).
STATUS 07:58: FLK_field (LEANFLK_FIELD) 290 s, 7 errors: chart (apply spv_inj: Fact synthesized before Kf known -> (spv_inj (Kf := Kf)), port patch), TC5_sum/diff/n2/n3/n4 (uY = ../2: ring1 cannot without CharZero, field fallback hit maxRecDepth -> set_option maxRecDepth 20000 in, port patches), SL_FL_C (NeZero 5 : C not found -> haveI NeZero 2/3/5 : C in K/w.tail). New FLK_field md5 bdfa679bab, TrK11 bc2fe8df1f, FLK_SLb d7621ba33b. Upstream L_gct_152 copied as lean/fl/kk152.part (namespace KK, theorem bilin_kernel, comments stripped; not yet compiled, not used by anything yet).
STATUS 08:00: TC5_sum/diff/n2/n3/n4 made char-free in the C source (z2.part: lemmas Y0_uY, Y1_uY via ← add_div/← sub_div + eq_div_iff two_ne_zero; the five proofs rewrite Y(.,0), Y(.,1) instead of unfolding uY/dY -> division-free ring1 goals). buildK: FLK_field 4f20faf49e (8032 lines), TrK11 6a9f290251; coordinator asked to swap the queued LEANFLK_FIELD2 / LEANTRK11B md5s. Backup leanfl/bak14/z2.part. Old TrK11 (d34ad9249a) still compiling since 07:53.
STATUS 08:01: coordinator: queue lines reference paths, so LEANFLK_FIELD2 / LEANTRK11B compile what is on disk (4f20faf49e / 6a9f290251). DO NOT run buildK.sh or change any part before they start.

STOPPED 08:04 UTC (Kevin aborted L-gct-210; no jobs running; files as listed in RESULT ROUND 15).
