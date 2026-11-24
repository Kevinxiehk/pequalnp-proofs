# L-gct-210: final master handover (work ABORTED by Kevin, 2026-11-24 ~08:05 UTC)

Lemma: every 5x5 level space (perm(J+t) = 120 on L) has dim L <= 8. Gap file lean/PEqualNP/Outside/L_gct_210.lean, allowed imports only
PEqualNP.Defs (gap.json). No PR was ever opened. No 9-dim level space was found, and nothing points to the lemma being false.

## Where everything is
- Full working tree (3.1 GB, on the local machine): /home/kevxhk/work/L-gct-210/ (+ /home/kevxhk/work/runs, /home/kevxhk/work/tools).
  The coord branch snapshot (local/final-2026-11-24/) holds the notes, scripts, Lean sources and small logs, not the caches or outputs.
- Start with PROOF-MAP.md (maintained by verify2): REMAINING-WORK TABLE at the top, then the UPSTREAM SHORTCUTS table and the branch-by-branch
  status (V-rN = verified by verify2 in round N).
- Per role: NOTES-<role>.md (RESULT block at the top, FINAL STATE / STOPPED line) and handover/HANDOVER-<role>.md.
  Roles: verify2 (independent verifier), verifyfl (SYM-M / [T22] / [DC3] pipeline), rows (leaf 3, (PL), (SM_n)), stage2 (branch 3, F2col,
  D003/D04), stage3 (branch 2, (S3-a), leaf 8), reg2 (branch 4, (S6-FO2), e <= 5), ncol ((6,2)/(7,3)), leanfl (SL/FL/TC5 in Lean, port to a
  field, certificate pipeline), leanzbf (zero-block chain R9f, R3-1 bundle R19bund).
- BRIEF.md: team rules, including 16a (staged refinement needs OPEN seed charts), 17 (junk-branch removal), 18 (memory during Lean compiles).
- COMPUTE-ERRATA.md: known tool pitfalls (msolve big coefficients, stale outputs, ...).
- Big-slot queue at the abort: /home/kevxhk/work/runs/bigq_extra.txt (done ids in bigq_extra.done); scheduler runs/bigq4.sh (re-reads the
  queue before every job); compile wrapper runs/leancompile.sh FILE TIMEOUT [EXTRA_AXIOM_NAMES]; generic Defs rebuild runs/defsbuild3.sh.

## Status at the abort (details in PROOF-MAP)
Closed or verified today (2026-11-24):
- TC5 over C is LEAN-COMPLETE (lean/fl/FLq2.lean, md5 11b60a129a: 0 errors, 0 sorry, standard axioms only).
- RED-p core formalised in Lean (leanfl/cert/Tcert.lean: valuation subring + projective normalisation + a chart certificate), 0 sorry.
- SYM-M [DC3] for |supp m| <= 3 complete at P1 (SYMDC3V2_A0); [T22] A case 0 down to two N-level batches (junk removal, verified).
- D003-PROP Case A closed (big-kernel lemma); D04-PROP closed in char 0 (verified by verify2 in round 25, with B(dep)'s two P0_B_i points).
- F2col CLOSED (verify2 round 25: every row audited, Kt3 re-run 20/20, the row-15 log checked plus a big-kernel second argument).
- Leaf 3: case G (support 4) and G4-A proved by hand (both verified); (SM5) proved in rank <= 2. Left: P2-z3, plus (SM5) in rank 3 or R4/R5/P2-A
  (REAL versions queued: R16P2z3R, R21W5R3P/Q, R17SMC5P/QR, R15R4QR/R5QR, R16P2AR).
- verify2 on Tcert: it matches RED-p at single-chart level; a full Lean RED-p still needs projective gluing over the whole Pluecker cover,
  certificates for every chart at one prime, and a #print axioms line.
- Leaf 8 (1,1,1,1,0): every special member found is closed, modulo PFC; completeness of the special list is still numerical.
- (7,3) case (C): H-a3/b22/b23-SL proved (verified); every known zero-free member excluded (330 systems, verified at 2 primes); the
  restricted classification is complete in (1,1) (verified by verify2, all 32 Case-C systems re-run); the r_a = 2 Plucker charts
  (NCOLK0Q, 42 jobs) were never run.
Refuted today (important for anyone resuming):
- (SM4) is FALSE (rank-2 counterexample, exact over Q(sqrt3, i)). PL4 is unaffected (own proof).
- CONJECTURE K0 is FALSE (exact counterexample family); the route goes through the restricted classification instead.
- No P4-free relaxation can prove (SM5) (explicit 5-column solutions).
Open leaves needing new mathematics (size L): (5,1) for |supp m| = 4, 5; (6,2)/(7,3) remainder; (S3-a); the other z patterns; (S6-FO2) for e <= 5
(3100|10000 is a rigid space with FO2 = 8 exactly, at the bound). Lean assembly: months-scale (leanfl's certificate-pipeline note: small
certificates cover about 90% of charts; certificate generation for the msolve-hard tail is the bottleneck).

## To resume
Read PROOF-MAP's remaining-work table, then the role handovers. Restart the scheduler with
  SKIPWIN1=1 SKIPST2X=1 SKIPC12=1 SKIPSYMC=1 SKIPWIN3=1 nohup bash /home/kevxhk/work/runs/bigq4.sh >> /home/kevxhk/work/runs/bigq3_driver.log 2>&1 &
after checking bigq_extra.txt (pending: everything not in bigq_extra.done). Keep pool jobs <= 0.5 GB resident, and one per helper during Lean
compiles (12 GB host; Lean compiles peak at 7-9 GB).
