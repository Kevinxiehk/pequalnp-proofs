# Computation requests (cloud → local), newest first

## 2026-11-23 19:58 — additions

| id | priority | spec | decides |
|---|---|---|---|
| VF-A-exact | 1 | VF-A redone over Q(θ) in Singular | turns the VF-A verdict into a proof |
| VF-F | 2 | `COMPUTE-verifyfl.md` F | residual kinds (R1)–(R4) for 3-column non-isotropic defect lines |
| ST2-S3 | 2 | `COMPUTE-stage2.md` S3 (exact) | the (2,4) family: Case B spaces are dead at first order |
| ST2-S1, S2 | 3 | `COMPUTE-stage2.md` S1, S2 | census of 5-dim 4×5 spaces with vanishing column-deletion permanents; any non-block solution? |
| ST2-S4 | 3 | `COMPUTE-stage2.md` S4 (exact) | minimal row pairs with zeros in the annihilators |
| REG2-E | 3 | `COMPUTE-reg2.md` census E and target (S6-FO2) | closes the regime "some row projection of dim ≤ 3" if negative |

Each request has an id; report under `local/results/<id>/RESULT.md` and add a line to `local/STATUS.md`.
Where a helper spec and HANDOFF.md overlap, the helper spec is the precise one.

## 2026-11-23 19:45 — initial list

| id | priority | spec | decides |
|---|---|---|---|
| C1 | 1 | `L-gct-210/handoff/HANDOFF.md` §2 C1 = `COMPUTE-rows.md` H1 = `COMPUTE-verifyfl.md` D | do 4×5 spaces with (dim, defect) = (5,1), (6,2), (7,3) exist? A hit gives an 8-dim 5×5 level space |
| VF-A | 1 | `COMPUTE-verifyfl.md` A (small, exact) | four explicit isotropic planes have no extension: one stratum of (5,1) |
| VF-B | 2 | `COMPUTE-verifyfl.md` B (exact, medium) | the N-problem for defect lines on 4 or 5 columns |
| S3-1 | 2 | `COMPUTE-stage3.md` 1 | a 9-dim level space containing a 2-dim single-row part? (could refute the statement) |
| R-H4 | 2 | `COMPUTE-rows.md` H4 | the 4×4 defect problem ((dim, e^col) = (5,1), (6,2)) |
| C2 | 2 | HANDOFF C2 = `COMPUTE-reg2.md` Census A, B = `COMPUTE-rows.md` H2 | are all 6-dim 4×5 level spaces "free row ⊕ 2" or "one neutral column"? any 7-dim one? |
| C3 | 3 | HANDOFF C3 = `COMPUTE-verifyfl.md` C | (SL_m) for sample defect lines |
| R-H3 | 3 | `COMPUTE-rows.md` H3 | independent test of the neutral-column law on fresh extremal spaces |
| REG2-C | 3 | `COMPUTE-reg2.md` Census C | 6-dim 4×5 level spaces with dim Ω ≥ 3 and no free row |
| S3-2..5 | 3 | `COMPUTE-stage3.md` 2–5 | cores of the 2-dim single-row case; exact confirmation of the plane lemmas |
| C4 | 4 | HANDOFF C4 | Lemma Z by saturation (off the critical path) |
| C5 | 4 | HANDOFF C5 | scale-ups of two searches that timed out |
| LEAN-1 | 3 | HANDOFF §3 | independent compile, axioms, linter verdict and byte sizes of the Lean files |

Corrections to specs will appear in `L-gct-210/COMPUTE-ERRATA.md` (a verifier is auditing them now).
