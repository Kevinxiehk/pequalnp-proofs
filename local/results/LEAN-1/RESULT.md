# LEAN-1 — independent compile, axioms, guard verdict, sizes (HANDOFF §3)

Toolchain leanprover/lean4:v4.36.0, repo upstream/main of 2026-11-23 ~18:00 UTC, prebuilt Mathlib cache.
Compiled with `lake env lean FILE` from the repo's lean/ directory; axioms via a copy with `#print axioms <final theorem>` appended.
"bundle" = L-gct-210-bundle.tar.gz Kevin downloaded at 19:29 Berlin; "branch" = coord-L-gct-210 at 0b205db (identical except FL.lean).

| file | bytes | errors | time | peak RAM | final theorem | axioms |
|---|---|---|---|---|---|---|
| lean/fl/FL.lean (branch) | 244 590 | 0 | 288 s* | 8.3 GB | L_gct_210_fl | propext, Classical.choice, Quot.sound |
| lean/fl/FL.lean (bundle) | 236 577 | 0 | 128 s | 8.2 GB | L_gct_210_fl | propext, Classical.choice, Quot.sound |
| lean/zbf/Zbf.lean | 96 823 | 0 | 88 s | 7.0 GB | L_gct_210_zbf | propext, Classical.choice, Quot.sound |
| lean/zbf/Zbf8.lean | 237 790 | 0 | 101 s | 7.4 GB | L_gct_210_zbf | propext, Classical.choice, Quot.sound |
| lean/zbf/Zbf9.lean | 242 907 | 0 | 140 s | 7.4 GB | L_gct_210_zbf | propext, Classical.choice, Quot.sound |
| lean/zbf/FrameZbf.lean | 163 925 | 0 | 70 s | 7.1 GB | L_gct_210_zbf | propext, Classical.choice, Quot.sound |
| lean/Frame210.lean | 67 231 | 0 | 62 s | 7.0 GB | L_gct_210_frame | propext, Classical.choice, Quot.sound |
(*) while 21 cores were busy with C1. Only deprecation warnings (if_pos / if_neg etc.).

## Guard (.github/scripts/outside-guard.mjs, `imports` command = import rule + plain-file rules + own-namespace rule,
judged as lean/PEqualNP/Outside/L_gct_210.lean): **all six REFUSED**, for two mechanical reasons only:
1. **Namespaces.** Helpers sit in `PEqualNP.Gct.FL210`, `PEqualNP.Gct.ZBF210`, `PEqualNP.Gct.F210`, `PEqualNP.Gct.Helpers.Minc`,
   `PEqualNP.Gct.Helpers.RankOne`, `PEqualNP.Gct.Kit086`, `PEqualNP.Gct.MethodCeiling`. Only `PEqualNP.Outside.L_gct_210` (or
   `..._aux`, or names below either) is allowed at top level; the final theorem must be `PEqualNP.Outside.L_gct_210`, last in the file.
2. **Lines beginning with `add_`** (read as the library's add_ commands): FL.lean line 4914; Zbf.lean 342, 1619;
   Zbf8/Zbf9.lean 342, 1619, 2070, 2596, 2662, 3038; FrameZbf.lean 1716, 2993. Fix: put other text first on the line
   (e.g. `exact add_mem ...` / `refine add_mem ...`) or wrap in parentheses.
No other plain-file violation was found (I ran checkPlain line by line, so block-comment edge cases are approximate).
Also note: the authoritative workflow only runs `check-lean.mjs ... check` — a refutation (negation) is REJECTED (statement); tested on PR 1628.
