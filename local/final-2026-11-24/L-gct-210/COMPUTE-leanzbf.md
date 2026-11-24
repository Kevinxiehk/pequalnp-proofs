# COMPUTE-leanzbf (L-gct-210, role leanzbf): compute jobs and their logs

## Round 10 jobs (2026-11-24, UTC; all python3 -I, ulimit -v 2500000, 1 core each, <= 2 at a time, timeout <= 1700 s)
- leanzbf/r3_dump.py p (p = 0..5): verify2/r3_exact.py + per-S record (dim Pi~_S, d, #factors). Logs r3_dump_p*.log, data
  r3_dump_p*.txt. Result: 132 configurations, 1169 certified cubics, d = 4 except 31 with d = 5 (all 1-factor); 12 survivors.
- leanzbf/r3_variant2.py p d4only: DFS ignoring the d = 5 triples. Log r3_variant_d4only.log. Part 2: 7 survivors (full: 4).
- leanzbf/r3_export.py p: exact per-(config,S) data (E basis of K_S, factors, k, u) -> r3_export_p*.txt (input of gen_e*.py).
- leanzbf/r3_minS.py p: greedy removal of column triples (0-factor first) keeping the DFS outcome identical; logs
  r3_minS_p*.log, data r3_minS_p*.txt (per configuration: #S, #kept, kept 0/1/3-factor, kept d's).
- leanzbf/gen_e3.py N, gen_e0.py N, gen_e1.py N: Lean generators (sympy), sample runs only (N = 2..3).

## Round 11 jobs (2026-11-24, UTC; python3 -I, ulimit -v 2500000, <= 2 cores, timeout <= 1700 s)
- leanzbf/r3_minS2.py p (p = 0, 2, 3, 4, 5): greedy triple removal with d = 5 triples dropped first; logs r3_minS2_p*.log,
  data r3_minS2_p*.txt. Result: only 3 configurations (part 2: 00012 with 00102 / 01002 / 10002, eps +1) keep a d = 5 triple.
- leanzbf/gen_cfg.py "<s12>" "<s13>" <eps> OUT: one configuration (E-lemmas, wrappers, DFS, inst). Runs: 01222/22001/-1
  (-> lean/zbf/r11_2.txt), 01222/22010/-1, 01112/00012/-1, 00012/00102/-1, 01222/10222/+1, 01222/10222/-1 (/tmp, 37-48 KB).
- leanzbf/gen_all.py K 12 (K = 0, 1): gen_cfg over the killed configurations (120 = 132 - 12 survivors), chunks of 12;
  logs gen_all_K.log, outputs leanzbf/cfg_out/*.txt (statistics on failures and sizes; not in any test file).
- leanzbf/gen_dispatch.py -> lean/zbf/r11_9.txt (f13_cases_* lemmas).

## Round 14 jobs (all 1 core, ulimit -v 2500000, <= 30 min, logs in leanzbf/)
- e5_search (01222/01222/-1, 04:05, < 1 min, e5s_01222_01222_m.log) and e5_search_all (11 survivors, ~3 min, e5_search_all.log).
- e5_gen_all (12 x gen_e5.py, ~2 min, e5_gen_all.log) -> e5_out/ (196 KB).
- surv_gen_all (12 x gen_surv.py, ~5 min, surv_gen_all.log) -> surv_out/ (~590 KB).
- compiled_map.py on R12s_combo_w0328.log (seconds).
