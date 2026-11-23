# Coordination branch for L-gct-210 (not a proof submission)

> **MIGRATION (2026-11-23 ~20:50 Berlin):** the cloud session has handed the whole effort to the local session.
> Start with `cloud/HANDOVER-MASTER.md`, then `cloud/L-gct-210/handover/HANDOVER-<role>.md`.


This branch exists only so that two Claude sessions working for the fork's owner can exchange notes,
computation specs and results on L-gct-210 (every level space of 5×5 complex matrices has dimension ≤ 8).
**Never open a pull request from this branch.** It shares no history with `main`.

## Layout

- `cloud/` — written only by the cloud session (the proof team).
  - `cloud/L-gct-210/handoff/HANDOFF.md` — status and computation tasks C1–C5 (read first).
  - `cloud/L-gct-210/COMPUTE-*.md` — exact computation specs written by the helpers;
    `COMPUTE-ERRATA.md` (when present) lists corrections to them.
  - `cloud/L-gct-210/BRIEF.md`, `NOTES-*.md`, `<role>/` (scripts, data), `lean/` (Lean sources).
  - `cloud/REQUESTS.md` — new computation requests, newest first, each with an id.
- `local/` — written only by the local 24-core session.
  - `local/STATUS.md` — one line per task: id, state (queued / running / done / failed), time, result file.
  - `local/results/<task id>/` — outputs: a short `RESULT.md` first (what was run, calibration outcome,
    counts, verdict), then data files (`.npy`, logs kept small).
  - `local/QUESTIONS.md` — questions for the cloud session.

## Protocol

- Each side writes only in its own directory, so merges never conflict.
- Before pushing: `git pull --rebase origin coord-L-gct-210` (or fetch + merge), then push.
- The cloud session syncs about every 10 minutes: it pushes refreshed notes and reads `local/`.
- Keep files small: no file over 20 MB, no build outputs.
- A result counts only with its calibration: say which planted or known solution the same code path
  recovered before a negative result is reported.

## Getting the branch (local session)

```
git fetch origin coord-L-gct-210
git worktree add ../coord-L-gct-210 coord-L-gct-210     # or: git checkout coord-L-gct-210 in a separate clone
```
