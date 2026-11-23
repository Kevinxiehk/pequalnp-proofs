# L-gct-210 — MASTER HANDOVER (cloud session → local session)

Written 2026-11-23, about 20:50 Europe/Berlin, by the cloud coordinator. From now on the local 24-core session is the
coordinator of the whole effort. The cloud session is shutting down; its workspace is mirrored in this branch.

Paths: `cloud/L-gct-210/` is the cloud team workspace (notes, scripts, data, Lean). `cloud/L-gct-210/handover/` holds one
HANDOVER file per helper, each written by that helper at the end. `cloud/tools/` holds the cloud tools (paths inside them
start with `/home/claude/...` and need adapting). `local/` is yours.

Model: Kevin asked to move back to **Opus** (Fable usage nearly exhausted); run helpers on Opus at effort **xhigh**.

---------------------------------------------------------------------------------------------------------------------
## 0. First 30 minutes (suggested)

1. Read sections 1–3 here, then `cloud/L-gct-210/handover/HANDOVER-verify2.md` (ledger: which results are verified),
   then the other HANDOVER files of the branch you start with.
2. Keep the desk lease alive (20 minutes past the last renewal; renew every 10 minutes; six hours at most, then release
   and ask again with `&hard=1`). Before any new work, check that no PR adds `lean/PEqualNP/Outside/L_gct_210.lean`
   (`cloud/tools/dupcheck.sh`).
3. Keep running what you have (C1, R6-1, VF-B, S3-1). Take over VF-NEXT yourself; the cloud's N1 generators are in
   `cloud/L-gct-210/verifyfl/exact/` (see HANDOVER-verifyfl for their tested/untested state).
4. Spawn helpers (up to 10, on this ONE lemma) for the roles in section 6, each with its HANDOVER file as the brief, and
   run the loop of section 7.

---------------------------------------------------------------------------------------------------------------------
## 1. The step and the rules

- **Statement (L-gct-210).** Every linear space L of 5×5 complex matrices with perm(J + t) = 120 for all t ∈ L (a "level
  space"; equivalently all subpermanent sums P₁..P₅ vanish on L) has dim L ≤ 8. The desk says "may be false": a 9-dim level
  space would refute it. Conjectured truth: the maximum is 7 = 2n − 3. Exact text: `cloud/L-gct-210/gap.json`.
- **Desk state (20:30).** The step is held by 10 agents (the parallel limit; you are one). Hard steps may be held by any
  number of agents, and the first accepted proof is merged. No PR on the step (checked every few minutes until 20:45).
- **Submission rules.** There must be exactly one file, `lean/PEqualNP/Outside/L_gct_210.lean`, of at most 512 KiB. It may
  import only `Mathlib` and `PEqualNP.Defs`. No sorry, axiom or native_decide. Format rules are in CONTRIBUTING.md (no
  comments, no double quotes, no `#` commands, restricted words and options). Guard rules: helpers go inside a namespace
  `PEqualNP.Outside.L_gct_210_aux` (or below it); the theorem `PEqualNP.Outside.L_gct_210` comes last; no line may begin
  with `add_`.
- **Check mode only.** A proof of the negation is REJECTED (your finding on PR 1628). A 9-dim space would only justify
  releasing the step as `statement_seems_false`, with the witness in the release notes.
- **Size cap.** The Lean written so far (FL ≈ 330 KB, Zbf strand ≈ 260 KB+) already exceeds 512 KiB and covers a fraction of
  the argument. Kevin's instruction: **ignore the cap for now** (compress later, or ask the project owner).
- **PRs.** This session could not open PRs upstream. Kevin opens them from a pre-filled compare link
  (`cloud/tools/prlink.py`). The template body is filled in, the optional X/LinkedIn fields are left empty, and the gap id
  and file name go in backticks.

---------------------------------------------------------------------------------------------------------------------
## 2. Proof architecture and state (20:45)

### 2.1 Approach (details: `cloud/L-gct-210/handoff/HANDOFF.md` §1, BRIEF.md UPDATEs 1–10)
- **R0:** L is level ⟺ perm = 120·ℓ⁵ on L̂ = ℂJ ⊕ L. **ZBF:** a zero block S×Z with |S| + |Z| = 5 factorises the permanent.
  This is how P₄ and P₅ enter; P₂ and P₃ alone cannot suffice (exact 9-dim space L9 in NOTES-repr).
- **Row invariants:** a_r = 5 − dim(row-r projection) ≥ 1; L_r = L ∩ {row r = 0} is a 4×5 level space; λ_{rr′}.
- **Lemma C** (all n, Lean): dim(L ∩ {rows r, r′ = 0}) ≥ dim L − 7. **C7:** minimal row pairs are Type I or Type II (Lean).
- **Defect normal form:** for 4×5 Y, c(Y)_j = perm(J₄ + Y minus column j) − 24. C(L′) = span c(Y), e = dim C. A (d,e) space
  lifts to a 5×5 level space of dim d + 4 − e (`handoff/oracle.py`, audited). The target (DI₅) is d ≤ e + 3; it suffices to
  exclude (5,1), (6,2), (7,3).
- **First-order tools:** FO/FO2: L ⊆ T₁(M), and L is totally isotropic for q_m (bilinear, not Hermitian), so
  dim L ≤ dim T₁(M) − ⌈rank/2⌉. **(FO-r)** (stage2 R7): the row-r projection of T₁(L_r) must be ℂ⁵. reg2: for every row r,
  dim L ≤ dim L_r + dim Ω(L_r) − 1.

### 2.2 Proved and verified bricks (the full ledger is in HANDOVER-verify2.md)
- **[Lean]** R0, ZBF, Theorem B, Lemma C, CA2, Theorem A, 3×3 level ≤ 3, N3′, C4, C7 classification, pigeonhole facts
  (Zbf strand); Lemma SL / Theorem FL (a strongly level 4×5 space has dim ≤ 3; a full free row or column forces dim ≤ 7),
  the defect construction, the hyperplane lemma, SL₃, NCOL-S (a), Lemma QB, FL45, R4.15 (F1)/(F2) (FL strand). All have
  standard axioms only and were compiled independently on your machine.
- **[verified]** Theorem GEN (all a_r = b_c = 1 with zero-free annihilators: impossible; one link is an exact ℚ(i) check on
  1,800 configurations); Theorem N, N2-X; S3-G; TC5, SPLIT, FS, PS, PR3, QB, SL3-RED, Lemma NP, Props I-ALL / II-ALL;
  NCOL-P3 (conditional on X4), P51, (SC1), NCOL2-P; cross-family theorem; Z22 (most steps); reg2 L1–L5 and M*.
- **New theorem today:** no principal (5,1) space for any defect line with three nonzero entries. The isotropic line
  (1, ω, ω², 0, 0) is settled by VF-A: unit ideal, projective system, three independent derivations (see verify2). The
  other lines are settled by PR3.
- **Correction from verify2 (20:40):** Theorem DC / NC′-DC (rows R5.2) — the claimed equality is wrong (counterexample in
  NOTES-verify2); use the inequality form. "(SL_m) ⟺ [DC3], [T22], [T31] empty" holds only in the direction ⟸.

### 2.3 The four open branches and what is left in each
1. **Defect inequality (rows, verifyfl).**
   - (5,1): open for non-principal cases, isotropic-split lines, |supp m| ≥ 4, repeated entries and kernel type (2,2,1).
   - The residual kinds (R1)–(R4) remain for 3-support non-isotropic m. Exact route: VF-NEXT [DC3], [T22], [T31] per m.
   - NCOL-P3 becomes unconditional if R6-1 (claims A, B) is unit.
   - (6,2), (7,3): via (SL_C) for defect spaces of dim e (verifyfl R5.10), or via (NCOL_e) + (DI_4x4) / (DC-COST) (rows).
   - This branch also decides stage2's z = 3 case and is the most advanced.
2. **Single-row elements, all a_r = 1, no minimal pair (stage3).**
   - Done: z = 0 is impossible (Theorem N); two rows with 2-dim single-row parts are impossible (Z22); z = (1,0,0,0,0) is
     closed except family F4b (an exact 7-dim core M₀ exists; need (i)–(iii) or FO2).
   - Open: F4b, z = (2,0,0,0,0) and the mixed patterns (1,1,..), (2,1,..).
3. **Minimal row pairs / REG1 (stage2).**
   - (FO-r) kills the generic (2,4) solutions and the whole cross family.
   - Left: z = 3 (which becomes a non-split (5,1), i.e. branch 1); (B0), an identically vanishing entry; Case B of the
     (2,4) family (exact task S3); B2.
   - Structural target: a (Q-r) solution passing (FO-r) and FO2 contains a 3-dim single-row part.
4. **Some a_r ≥ 2 (reg2).**
   - a_r = 2 at dim 9 is impossible if (S6-FO2): every 6-dim 4×5 level space without a full free row has FO2 bound ≤ 8.
   - Families with a 3-dim single-row part (M*, EC moves, DR3) are excluded by a hand proof (20:08, NOT yet verified).
   - The NC family and support pattern (2,2|2) are settled exactly with msolve/Singular (20:25, NOT yet verified).
   - Open: the remaining families; "every 6-dim 4×5 level space has a deletable row or column"; a_r = 3 (no 7-dim 4×5
     level space is known).

**Evidence on the other side:** no 8-dim level space was ever found (structured, seeded and extension searches). C1 has
0 confirmed (5,1) / (6,2) / (7,3) hits so far, with calibrations passing. Random-start LM is unreliable at n = 5.

### 2.4 Honest estimate (cloud view at 20:45)
- **Paper proof:** about 10% within a day; 15–30 more helper-hours with no guarantee. The exact engines on both machines
  are what is moving things fastest.
- **Lean:** a complete formal proof along this route would be several megabytes, beyond the cap as the rules stand.

### 2.5 Last changes, 20:30–20:45, from the helper handovers. These override anything above.
- **rows:** claim (A) of R6-1 is FALSE. A strongly level 4×5 matrix with five nonzero columns exists
  (`rows/sle5_s1005.npy`). R6-1 must therefore run the plane cases **B and C** (B3 and A4 remain calibrations); see
  COMPUTE-rows.md "NEW (round 6)". The calibration A4 did not finish in 100 s on the cloud.
- **stage3:**
  - [exact] the free-column sub-family of F4b is impossible: unit ideal on all 81 charts, over ℚ with Singular and mod 3
    primes with msolve, with the level-only calibration non-unit.
  - Parallel y_a..y_d force that sub-family, so F4b is open only for non-parallel y_r.
  - Next idea: a "four lines and a plane" lemma, tested first by a 30-unknown msolve run (HANDOVER-stage3 §3).
- **verifyfl:**
  - In `verifyfl/exact/`, `exactlib.py`, `gen_n1.py` and `gen_n1s.py` pass their substitution tests; `gen_n2.py` ([T31])
    and `gen_n3.py` ([T22]) are NOT written.
  - [modular, one prime] the cross-checks Lemma 3C and Lemma SL come out unit.
  - [DC3] for m = (1,2,−3,0,0) is unit in 252 of 254 structured cases. The two generic rank-2 cells timed out and are saved
    as `.ms` files in `exact/run/`, so there is no [DC3] verdict yet: run those two cells on 24 cores first.
- **reg2:**
  - (S6-FO2) is proved by hand (SP8) for every family with a 3-dim single-row part.
  - [exact over ℚ] it also holds for the NC family, pattern (2,2|2) and pattern (2,1,1|2) case (iii).
  - **UNDECIDED:** pattern (2,1,1|2) case (ii), where the exact Ω-test is non-unit in chart (1,2,3). This is task T1;
    `reg2/dr211b_num.py` is written but not run.
- **stage2:**
  - Case B of the (2,4) family is now fully parametrised. This CORRECTS round 7's "Ω = span(e₀, 1) on all of Case B":
    dim Ω is 3 or 4 on special loci, never 5 in 47 members (unproved).
  - Three Singular runs timed out. New tasks S3′ and S7 are in COMPUTE-stage2.md; the 18 candidate arrays are in
    `stage2/data/`.
- **Lean, final states:**
  - `lean/fl/FL.lean` = FL.v32: 7,451 lines, 341,940 bytes, about 4.5 min to compile here, no hypotheses.
  - `lean/zbf/R3e.lean` (= R3e_ok): 5,914 lines, 290,918 bytes; T1, T2, T2″ and R3-1 are stated as explicit hypotheses.
  - Both use standard axioms only and pass the format and guard checks.
- **Still unverified** (verify2's list): verifyfl R5.9 (Props I-ALL, II-ALL); stage3 rounds 7 (final part) and 8; reg2's SP8
  and its exact runs; rows R6; stage2 R8; the VF-B main cases.

---------------------------------------------------------------------------------------------------------------------
## 3. Computation queue (your machine) and specs
- **Requests:** `cloud/REQUESTS.md` (newest first). **Answers to your questions:** `cloud/ANSWERS.md`.
- **Specs:** `cloud/L-gct-210/COMPUTE-{rows,verifyfl,stage2,stage3,reg2}.md` and `handoff/HANDOFF.md` §2.
  **Read `COMPUTE-ERRATA.md` first** (six errors are corrected there).
- **Running at 20:27 (your STATUS):** C1 (three streams), R6-1 (A, A4, B, B3 at P1), VF-B (main cases), S3-1.
- **Pending, in priority order:**
  1. VF-NEXT (N1–N6; generators in `verifyfl/exact/`)
  2. R6-1 at more primes
  3. VF-F, ST2-S3, R-X5
  4. R-X1..X3, R-H3b, ST2-S1/S2/S4 (S4 needs the normalisation fix from verify2), REG2-E
  5. R-H4, C2, C3, R-H3, S3-2..5, C4, C5
- **Exact-verdict rule:**
  - A homogeneous (projective) system that is unit at one good prime is a proof.
  - An affine or saturated system is evidence until it is run over ℚ (or the number field).
  - Every claim of a unit ideal needs a calibration that comes out non-unit.

---------------------------------------------------------------------------------------------------------------------
## 4. Lean
- `cloud/L-gct-210/lean/fl/FL.lean`: latest compiling version of the FL strand (see HANDOVER-leanfl for version and size).
  `FL.v*.lean` are older versions.
- `cloud/L-gct-210/lean/zbf/`: Zbf11 → R3a → R3b → R3c → R3d → R3e (`*_ok.lean` = compiling snapshots); see
  HANDOVER-leanzbf.
- `cloud/L-gct-210/lean/Frame210.lean`: the bridge from the desk statement to the internal formulation (d = 0 case and WLOG).
- **Compile:** `lake env lean FILE` from the repo's `lean/` directory. `cloud/tools/leancheck FILE [gap.json]` appends
  `#print axioms`, counts format violations, checks the guard rules and limits itself to 2 parallel compiles. On your
  machine: FL ≈ 207 s and 8.4 GB; Zbf11 ≈ 185 s.
- **Rule:** formalize only results that a verifier has VERIFIED. Anything not proved is stated as an explicit hypothesis,
  never hidden.

---------------------------------------------------------------------------------------------------------------------
## 5. Kevin's standing instructions (all still in force)
- Work only on this one hard lemma with up to 10 helpers; never claim several desk steps in parallel.
- "Forget the 45 m limit, keep going as long as it is potentially realistic"; "be more aggressive on tackling hard
  directions"; "be creative and persevere, since this would be a genuinely new lemma if proven/refuted".
- Every message to a helper includes the motivation and a reminder to be creative and persistent.
- **Checkpoints every 3–4 minutes:**
  - a short high-level progress summary;
  - the gap to a complete proof, and how long closing it would likely take;
  - whether a PR exists on the lemma;
  - the fork kept up to date with upstream;
  - any new computation tasks.
- Sketch the Lean proofs as you go, with separate Lean helpers formalizing verified paper results. Keep formalizing; ignore
  the size limit for now.
- Releases carry notes on what was done and what did not work, "so other people don't try the same things".
- Before starting any lemma, check that no PR on it exists.
- Usage: Kevin checks usage himself. The original instruction was not to exceed 90% of the weekly limit. Use Opus now.

---------------------------------------------------------------------------------------------------------------------
## 6. Team: roles and handover files (`cloud/L-gct-210/handover/`)

| role | branch / job | HANDOVER file | notes / compute |
|---|---|---|---|
| rows | defect inequality: NCOL, DI_4x4, DC-COST, principal kernels | HANDOVER-rows.md | NOTES-rows.md, COMPUTE-rows.md |
| verifyfl | (SL_m) / (SL_C); exact pipeline N1–N6 | HANDOVER-verifyfl.md | NOTES-verifyfl.md, COMPUTE-verifyfl.md |
| stage2 | minimal row pairs, REG1, (FO-r), (B0) | HANDOVER-stage2.md | NOTES-stage2.md, COMPUTE-stage2.md |
| stage3 | single-row elements: F4b, z = 2, mixed z | HANDOVER-stage3.md | NOTES-stage3.md, COMPUTE-stage3.md |
| reg2 | regime a_r ≥ 2: (S6-FO2), 6-dim 4×5 taxonomy | HANDOVER-reg2.md | NOTES-reg2.md, COMPUTE-reg2.md |
| verify2 | independent verifier + spec and generator auditor | HANDOVER-verify2.md (ledger) | NOTES-verify2.md, COMPUTE-ERRATA.md |
| leanfl | Lean, FL strand | HANDOVER-leanfl.md | NOTES-leanfl.md, lean/fl/ |
| leanzbf | Lean, Zbf strand | HANDOVER-leanzbf.md | NOTES-leanzbf.md, lean/zbf/ |

Earlier roles, finished; their notes are still useful background:
- adversary, numerics, repr, lowd, growth (searches; L9; the pitfalls of LM)
- chief (Type I′, pigeonholes); dc5, split, zeros, hessmix, kbuild, lemmaz, methods
- lean (Frame210), verifyfl rounds 1–3 (independent proof of FL)
- the verify team (GEN)

---------------------------------------------------------------------------------------------------------------------
## 7. WORKING STYLE of the cloud session (as requested by Kevin)

**Organisation**
- One coordinator, many specialists. The coordinator does no deep mathematics itself: it routes work, keeps the shared
  brief current, merges news across roles, guards rigour and reports to Kevin. Up to 10 helpers, all on the one hard lemma.
  Roles are cut along the proof's branches, plus two kinds of non-authors:
  - independent **verifiers**, who re-derive and never trust the author;
  - **Lean formalizers**, who only build on verified results.
- Helpers run on the strongest available model at effort xhigh. Running helpers are not restarted when settings change;
  new settings apply to new or resumed helpers.
- **Rounds.** Each helper works in rounds of about 1–2 hours with numbered targets in priority order. A round ends with a
  final report whose bottom line comes first, rigorous results separated from numerical ones, then the files. The
  coordinator assigns the next round immediately on receipt; a helper should never sit idle while there is a promising
  target.
- **Messages to helpers always contain:**
  - the motivation (L-gct-210 would be a genuinely new lemma if proven or refuted) and a reminder to be creative and
    persistent;
  - specific praise of what worked;
  - cross-team news that bears on their problem (who proved what, which tool now exists, which claim was refuted);
  - ordered targets, the discipline rules and the compute budget.

**Files**
- One `NOTES-<role>.md` per helper:
  - a RESULT block at the top, always current;
  - sections appended per round, never rewritten — superseded claims are flagged in place;
  - `STATUS hh:mm: …` lines every 10–15 minutes, which the coordinator reads with `grep '^STATUS' | tail -1`.
- Helpers read everything and write only their own files.
- A shared `BRIEF.md` carries numbered UPDATEs for team-wide facts: new tools, corrections, verified theorems, rules.
- Heavy computations are written as specs in `COMPUTE-<role>.md`: definitions, script, command line, calibration and
  decision rule.

**Rigour discipline**
- **Labels:** [rigorous] (hand proof), [verified] (re-derived by a verifier), [Lean], [exact], [modular], [numerical].
  Refuted conjectures are recorded as REFUTED and never quietly dropped — including our own (S6′), (B), (C*), "P₂/P₃ cap at 7".
- **Numerics:**
  - calibrate every search on planted or known solutions first, and report the calibration rate beside the target count;
  - random-start LM is unreliable at n = 5; prefer seeded one-vector extension;
  - use relative rank tolerances of about 1e-4 on LM output, and polish to 1e-12 before deciding invariants;
  - take at least as many sample points as monomials, and test every hit at fresh points plus `oracle.py`;
  - all forms are bilinear, never Hermitian (the conjugation pitfall).
- **Exact computation:**
  - pure-Python generators with modular arithmetic write msolve or Singular input;
  - use at least 3 primes and all coordinate charts, with calibrations in both directions;
  - for a projective system, one good prime is a proof; otherwise run over ℚ before calling it a theorem;
  - replicate decisive verdicts with an independently written generator.
- **Verification:** a separate verifier re-derives every hand proof (VERIFIED / GAP / ERROR, with repairs), audits every
  compute spec before it is run (COMPUTE-ERRATA.md) and audits generator scripts line by line.

**Compute policy**
- The cloud session had 2 shared cores, so only seconds-to-minutes jobs ran there. Anything heavy went into a spec, was
  audited, and queued in `cloud/REQUESTS.md` for the 24-core machine; results came back in `local/results/<id>/RESULT.md`.
- After the move, the local machine does both. Keep the spec → audit → run → RESULT pattern anyway, because it caught six
  errors before they cost hours.

**Coordinator loop** (every 3–4 minutes per Kevin's latest instruction; earlier every 10)
1. `dupcheck.sh lean/PEqualNP/Outside/L_gct_210.lean` — has someone opened a PR on the step?
2. `sync.sh` — push upstream `main` to the fork's `main` and rebuild Defs if needed ("keep our fork up to date").
3. `coord_sync.sh` — push the notes, read the other side's changes (no longer needed once everything is local).
4. Read every helper's last STATUS line; process final reports; assign next rounds; route new compute tasks.
5. Send Kevin a short message:
   - what changed (no repetition);
   - the gap to a complete proof and an honest time estimate;
   - new computation tasks;
   - any constraint the moment it is noticed (as with the size cap).

   Never claim a proof that has not been verified, and give probabilities rather than hopes.

**Desk etiquette**
- Never several steps in parallel.
- Renew the lease on schedule.
- Release with an honest reason and a summary of what was tried and what failed.
- Check for existing PRs before starting and before pushing. Three of our early PRs were rejected as duplicates.
- One branch, one commit, one file.

**Communication with Kevin**
- Short high-level summaries; the bottom line first; only the changes since the last checkpoint.
- Clear yes/no on PRs and the fork.
- Questions only when a decision is really his (for example, installing software on his machine).

---------------------------------------------------------------------------------------------------------------------
## 8. Tools (copies in `cloud/tools/`; adapt the paths)
- `leancheck FILE [GAP.json]`: compile against the shared build, print axioms, check format and guard, verify the
  statement verbatim.
- `dupcheck.sh FILEPATH`: fetch all upstream PR heads and list the PRs that add FILEPATH (and whether it is already on
  main).
- `sync.sh`: sync the fork's `main` with upstream and list new files.
- `coord_sync.sh`: this branch's sync (the cloud side).
- `prlink.py`: build the pre-filled PR compare link (template body, backticks, optional fields empty).
- `poll.sh`, `poll20.sh`, `reclaim.sh`, `beat.sh`: old desk scripts — superseded by `tools/pnp.sh` in the repo; do not use.
- `cloud/L-gct-210/handoff/oracle.py`: reference checker for (d,e), lifting and level errors (audited, correct).
- Gröbner engines: msolve and Singular (the cloud used the PyPI wheels `passagemath-msolve` and `passagemath-singular`,
  binaries under `site-packages/sage_wheels/bin/`).
