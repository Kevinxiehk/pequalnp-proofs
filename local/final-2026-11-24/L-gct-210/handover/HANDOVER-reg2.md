# HANDOVER reg2 (L-gct-210, leaf S6-FO2 / e <= 5 types) -- work ABORTED by Kevin, 2026-11-24 ~08:03 UTC

Full record: NOTES-reg2.md (RESULT blocks on top; sections 19-28), tools: COMPUTE-reg2.md sections 10-13, everything under reg2/.
Evidence logs: reg2/evidence/logs/ (r11_* .. r20_*).  No own jobs are running.

## State of the main results
- e = 6 (line-spanned) patterns: all closed exactly (rounds 11-15).
- e = 5 types: 296 types / 1370 classes; stage 1 exact (452 empty line configurations, 214 incidence kills, 66 type kills; 630 classes with
  components, 74 stage-1 timeouts).  Numerical measure (26.1): nothing survives at GENERIC points of any component, but genuine members exist
  on special loci (26.6).
- Known genuine e = 5 members and FO2 (27.3, 28.1): ext_9..11 (2100|20000) (9,3,7); dr35_u2_s52_400 (2200|10000) (9,3,7);
  dr35_u3_s41_116/_29 (3100|10000) (10,4,8) -- now EXACT: the 3100|10000 R1 type on the line-free pair is the single rigid space c3100
  (gen_rank.py FAMS 'c3100'), level, dim T_1 = 10, rank q = 4, FO2 = 8 (r20_c3100_exact.log).  Leaf statement for e = 5 must be
  "every member has FO2 <= 8", not "no member exists".
- Rank-one lemma (27.1, 27.7; rigorous, partial): a genuine two-row element is rank one (z = x + y = 0) when the other two rows carry (3,1)
  lines, (2,2) lines (except U_k = U_l totally isotropic), and for column patterns (3,0,0), (2,1,0), (1,1,1) (except three proportional
  column lines): 42 of 630 classes.  Open: other-row patterns (3,0), (2,1) (partly via 27.1(4)-(5)), (2,0), (1,1), (1,0), (0,0).
- Lemma N0 (N reduces to R1 if Lin(M) has a cross element on the pair), Lemma N1 (26.2).
- (3,1|2) along (1,1,1): CLOSED exactly (26.5, 27.4).
- R3: case (II) at two rational B and case (alpha) at one rational point closed (cone argument; absolute irreducibility checked by Hessian
  rank 3, 27.5).  Case (I) at its rational point: V_B contains five 3-dim linear spaces (exact over Q) but all give degenerate M (block of
  rank 2 modulo Lin, e = 4, FO2 7); gap: other Qbar-subspaces with the same reduction mod p (27.6).  Generic parameters of all R3 cases: open.

## Batch scripts (queued by the coordinator, not run by reg2)
- REG2E5BATCH: reg2/e5/batch_e5.py STAGE1_LOG OUT TMO -- resumable, one verdict line per type, full exact stage 2 via reg2/e5/twostage.py
  (genuineness fixed in round 18: R1/C1 saturate by maximal minors of [U_P; x], [U_Q; y]); EMPTY verdicts are final, NONEMPTY/TIMEOUT need
  inspection (members exist on special loci).
- LOW_REG2E5SPLIT: same driver with a 4th argument (earlier batch output) reruns NONEMPTY/TIMEOUT types with RANK1SPLIT=1.
- twostage.py modes: RANK1SPLIT, DROPU (Lemma split), RANKDROP, LINEAR_ONLY, STAGE1_ONLY; on member-carrying types the exact calls time
  out (120-400 s) or exceed 0.5 GB -- those types need parametrisation + FO2 certification (as done for c3100), not Groebner emptiness.

## Corrections made in place (for verifiers)
- 24.5 / R16-5: the cone result belonged to case (alpha), not (I) (26.4).
- 20.1 / 24.5: the cone argument needs absolute irreducibility (27.5) -- verified for (II) and (alpha).
- R17-2 "264 classes with a free direction" were mostly gauge directions (26.1).
- twostage.py pre-round-18 NONEMPTY verdicts for R1/C1 are unreliable (gauge); EMPTY verdicts remain valid.

## Next steps if resumed
1. N element of the 3100|10000 pair (stage2g RANK1 run was stopped); other pairs of that pattern.
2. Exact parametrisation + FO2 certification of the 2100|20000 (ext) and 2200|10000 (dr35_u2) families (likely rigid as well; same
   method as 28.1).
3. Rank one for the (2,1)/(3,0) other-row patterns via the cross lines.
4. R3 (I): Fano-scheme reducedness / second lift; generic parameters.
