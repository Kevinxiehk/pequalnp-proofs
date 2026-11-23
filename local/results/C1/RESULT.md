# C1 — (5,1), (6,2), (7,3) existence searches   [PARTIAL, updated 19:27 UTC]

Solver: your rows/clm.py unchanged (holomorphic LM, analytic Jacobian, Grassmannian chart), driver `c1multi.py` (attached):
N = 140 / 160 / 260 / 420 sample points for d = 4 / 5 / 6 / 7 (errata A5), HIT = res < 1e-9 and cond < 1e6, then polish
(solve from the hit, tol 1e-13), then handoff/oracle.py on every hit: CONFIRMED = oracle dim = d, 4x5 level error < 1e-8 and
lift level error < 1e-8 at fresh points. A target counts iff CONFIRMED with oracle d - e >= 4 (errata C1 [B]).
Three streams, 7 processes each (your 19:58 split): unseeded / seeded (rows/seeded.py start: known (d-1, e_old) space + one
random direction, scales 1, 0.3, 3) / nc (rows/ncdef_search.py PN, column 0 neutral).
Seed pool: your rows/*.npy (clm_p4_*, seed_*, c52_*, nc_*, ncdef_*) + my calibration hits, classified by the oracle:
(4,1): 359, (5,2): 209, (6,3): 55 spaces (also (3,0): 2, (3,1): 6). No (5,1) or (6,2) seed exists.

## Calibrations (all hits oracle-confirmed; no unconfirmed hit so far)
| variant | case | N | starts | hits |
|---|---|---|---|---|
| unseeded | (4,1) | 140 | 500 | 183 |
| unseeded | (5,2) | 160 | 500 | 82 |
| unseeded | (6,3) | 260 | 500 | 20 |
| seeded (4,1) -> (5,2) | (5,2) | 160 | 300 | 98 |
| nc (1 neutral col) | (4,1) | 140 | 300 | 118 |
| seeded (5,2) -> (6,3) | (6,3) | 260 | 300 | running |
| nc | (5,2), (6,3) | | 300 each | running |

## Targets (running; counts so far)
| variant | target | starts done | confirmed hits with d - e >= 4 |
|---|---|---|---|
| unseeded | (5,1) | running (2000 per round, then (6,2), (7,3); 6 rounds) | 0 so far |
| seeded (4,1) -> (5,1), (5,2) -> (6,2), (6,3) -> (7,3) | | queued after calibration | |
| nc | (5,1), (6,2), (7,3) | queued after calibration | |
(An earlier unseeded (5,1) run at N = 140 was discarded after your N correction.)
