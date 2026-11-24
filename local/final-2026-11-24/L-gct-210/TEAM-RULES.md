# TEAM RULES — L-gct-210 team on Kevin's machine (coordinator: the local Claude Code session). Written 2026-11-23 19:45 UTC.

WHY: L-gct-210 (every linear space L of 5x5 complex matrices with perm(J+t) = 120 on L has dim L <= 8) would be a GENUINELY NEW
lemma if proven or refuted. A 9-dim level space refutes it. Be creative and persistent: try the obvious route, then the strange one;
when a route stalls, look for a different invariant, a different normal form, or an exact computation that decides a case outright.

## Machine and paths
- Workspace root: /home/kevxhk/work/L-gct-210   (= cloud/L-gct-210 of the old branch; all /home/claude/work/... paths were rewritten;
  if a script still says /home/claude, adapt it).  Other notes: /home/kevxhk/work/L-gct-086.  Tools: /home/kevxhk/work/tools.
- 24 cores, 12 GB RAM (+8 GB swap), Ubuntu 24.04. Engines: /usr/bin/msolve (0.6.5; `msolve -g 2 -t THREADS -f in.ms -o out`),
  /usr/bin/Singular (4.3.2; NOTE: `sat(I,J)` returns the IDEAL directly in this version — do not write `sat(I,J)[1]`; use
  `sat_with_exp` for the exponent). Python 3.12 with numpy, scipy, sympy 1.12, mpmath. Run Python as `python3 -I`.
  Do not install software (ask the coordinator instead).
- Lean: `/home/kevxhk/work/tools/leancheck FILE.lean [GAP.json]` (compiles against the repo's Mathlib + PEqualNP.Defs, prints axioms,
  time, peak memory, guard/format report). ONE compile at a time machine-wide (each needs ~8 GB): leancheck waits for the slot.
  Never run `lake build` or `lake env lean` directly; never touch the git repos.

## Compute budget (shared machine — the coordinator also runs C1, VF-B, R6-1 and others)
- Your own jobs: at most 2 cores at a time, at most ONE job above 0.5 GB at a time and at most 2 GB each (`ulimit -v 2000000`), at most ~30 minutes each, in the background (see BRIEF UPDATE 12: memory is the hard limit)
  with a log in your directory (print incrementally; a killed foreground job loses everything).
- Anything bigger (more cores, hours, many primes x charts): write it as a spec in your NOTES (or COMPUTE-<role>.md) with command
  line, calibration and decision rule, and add one line to /home/kevxhk/work/QUEUE.md: `ROLE | id | command (cwd) | cores | est. time | why`.
  The coordinator schedules it and writes the result path back into QUEUE.md.
- Running jobs and their outputs are listed in /home/kevxhk/work/RUNS.md (read it; do not duplicate a running job).

## Files and communication
- Read anything; write ONLY your own files: NOTES-<role>.md, COMPUTE-<role>.md, your directory <role>/ (scripts, data, logs), and
  handover/HANDOVER-<role>.md at the end. BRIEF.md and TEAM-RULES.md are the coordinator's.
- NOTES-<role>.md: RESULT block at the top (always current); append a section per round, never rewrite; flag superseded claims in place.
- Write a line `STATUS hh:mm: <one line>` (UTC) at the end of your NOTES every 10-15 minutes. The coordinator reads `grep '^STATUS' | tail -1`.
- No git, no GitHub, no desk (pequalnp.com) calls, no pull requests: the coordinator holds the lease and does all of that.

## Rigour discipline (from verify2's ledger — each pitfall bit somebody)
- Labels: [rigorous] hand proof, [verified] re-derived by a verifier, [Lean], [exact], [modular], [numerical]. Refuted claims are
  recorded as REFUTED, never quietly dropped.
- All pairings BILINEAR (no conjugation). Null spaces from SVD: N = vh[r:].conj().T and Gram N.T @ Q @ N.
- Sampling: at least as many points as monomials (better 2x) and a fresh-point test + handoff/oracle.py on every hit.
  Random-start LM is unreliable at n = 5: calibrate every search on planted/known solutions of the same kind and report the rate.
- Mod-p Groebner verdict = PROOF in char 0 only for a projective system covering all points (homogeneous / all charts / all cells and
  cases), no saturation, no open condition, constants realised mod p with their Galois conjugates covered. Otherwise EVIDENCE until run
  over Q (or the number field). Use >= 3 primes, calibrations in both directions, and an independent generator for decisive verdicts.
- Watch for: "iff" where only one direction is proved; "=" where only "<=" holds; unchecked independence of annihilators; a missed
  sub-case of a case split; zero entries in an annihilator assumed away.
- Formalize in Lean only results a verifier has VERIFIED; anything unproved enters as an explicit hypothesis, never hidden.

## Rounds
- Work in rounds of about 1-1.5 hours with ordered targets. End each round with a final report (your last message): bottom line first,
  rigorous results separated from numerical ones, then files and the next targets you propose. The coordinator assigns the next round.
