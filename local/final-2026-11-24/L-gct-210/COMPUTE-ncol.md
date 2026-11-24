# COMPUTE-ncol (role ncol). All jobs small (<= 0.2 GB, 1 core each), run locally; nothing queued in QUEUE.md this round.

## Done (round 1)
| id | what | command (cwd ncol/) | result | label |
|---|---|---|---|---|
| IV2-msolve | config (a) sub-case (iv-2): Q in Gr(3,8), rows in U = {sum 0, x0 = x1}, Q level + row deletions level | `python3 -I gb/iv2gen.py P iv2 gb/iv2_P; gb/runall.sh gb/iv2_P` for P = 2147483629, 2147483497, 2147483077 | UNIT in 56/56 Pluecker charts at all 3 primes (< 0.1 s/chart) | modular; projective, no saturation => char 0 by RED-p |
| IV2-cal | same generator, U = span(chi, e_0 - e_3) (contains the known C^S (x) chi) | `python3 -I gb/iv2gen.py P cal gb/cal_P; gb/runall.sh gb/cal_P` | NON-unit in 32/56 charts at all 3 primes; chart 012 contains m = 0 = C^{012} (x) chi | calibration passed |
| CHI-exact | defect dim of (C^{012} (x) chi | 0) + (0 | 1^perp) | `python3 -I caseA_chi_exact.py` | exact rank 3 over Q(i) | exact |
| CASEA-LM | (6,<=2) with full free column (L' = (Q|0) + (0|1^perp)) | `caseA_search.py 3 2 0 400 900` | 0/264, residual floor 3.4 | numerical |
| CASEA-cal | same shape: (5,<=2) and (6,<=3) | `caseA_search.py 2 2 0 3 80`, `caseA_search.py 3 3 0 20 120` | 3/3 and 13/20 (oracle level <= 3e-13) | calibration |
| IV2-LM-ctl | 3-dim row-strongly-level Q with rows in 1^perp (no equal columns) | `iv2_search.py free 0 4 150` | 4/4 | control for iv2_search.py |
| X2 | rows' X2: (6,3) spaces containing e_0 (x) C with C = V_012 + V_34 fixed, defect inside C | `x2_search.py b32 0 600 1500` | see NOTES-ncol (0 hits so far) | numerical |
| X2-ctl | same with C = V_0123 (neutral column 4) | `x2_search.py b41 100 200 600` | 83/100 found, all oracle-confirmed (6,3) | calibration |

## Proposed (next round)
- Configurations (b), (c), (d) of C3 (NOTES-ncol N1.3) as projective systems in the style of IV2 once the hand reduction (pairings of
  X_n with rows, (F1^T)) has cut them to small Grassmannians; (d) is "6-dim 4x4 level spaces Q with a twisted column", Gr(6,15): too big
  directly -- needs the hand structure first (or the upstream n = 4 bound <= 5, "L-gct-091", which would kill (d) outright).

## Round 2
| id | what | command (cwd ncol/) | result | label |
|---|---|---|---|---|
| FIXW | (6,3) with C(L') inside w^perp, w fixed | `fixw_search.py {ctl,iso1,iso2} ...` | ctl (1,1,1,1,-4): 3/52; iso2 (1,i,-1,-i,0): 0/105; iso1 (1,w3,w3^2,0,0): 0/116 | numerical |
| SROW | single-row / single-column parts of known (6,3) spaces | `srow_chk.py FILES` | 23/23 have a single-row element; all have a single-column element in the neutral column | numerical |
| CC3-msolve | CC3 full system, Gr(4,10) x P^3, 24 orbit charts | `gb/cc3gen.py`, `gb/runlog.sh` | msolve SEGFAULT at the 2 GB cap (44 s); Singular > 1 GB after 6 min (stopped) | not usable at 2 GB |
| CC3-survivors | the three survivor systems of the hand analysis | `python3 -I cc3/survivors.py` | Groebner basis [1] over Q (sympy, exact) for (4,0), (2,2) orient 0, (2,2) orient 1 | exact |
| CC3-cal | same systems without cubic conditions / with F3 only / d3 only | `python3 -I cc3/survivors_cal.py {none,F3,d3}` | none: consistent (non-unit); F3 only: unit; d3 only: unit | calibration |
| CC3-LM | column-centred 3x5 (4,<=1) by LM | `cc3_search.py 4 1 0 200 600`; calibrations `2 0` (3/4), `4 2` | see NOTES R2.13 | numerical |
Prepared but NOT queued (the hand proof made it unnecessary): `gb/cc3_queue.sh` (24 orbit charts x 3 primes + D = 2 calibration, ULIM 8 GB).

## Round 3
| id | what | command (cwd ncol/) | result | label |
|---|---|---|---|---|
| STALE | E-STALE-OUTPUT check: runners patched, all earlier verdicts re-run | `gb/runall.sh DIR`, `cc3/survivors_ms.py P` | all reproduced (iv2 56/56 UNIT x3, cal 32 NONUNIT x3, e3planes 10/10, survivors UNIT) | modular |
| CC-FREE | column-centred 3x5 level spaces, no defect condition, by LM | `cc3_search.py 3 -1 ...`, `4 -1 ...`, `4 3 ...`, `4 2 ...` | dim 3: 30/30; dim 4: 4/58 (e = 4); (4,<=3): 4 hits (e = 3); (4,<=2): 0; all dim-4 hits product type | numerical |
| E3P | e_3 vanishes on no 3-dim subspace of C^5 | `gb/e3planes/` (10 charts of Gr(3,5)) | UNIT 10/10 at 3 primes | modular, projective |
| FREE4 | full no-defect Gr(4,10) system | `gb/freegen.py`, orbit charts | msolve segfault at 2 GB (86 s) -> queued as PROD-NCOL (8 GB, big slot) | -- |
| EXACT-EX | W (+) W, W = span(e_0, (0,1,i,-1,-i)) | `exact_prod.py` | level, column-centred, defect 3 (exact) | exact |
| PROD-E2 | product type, defect <= 2 | `gb/prod/prodgen2.py P 2 DIR reps_e2.txt`; `gb/runlog.sh` | UNIT 11/11 orbit charts at P1 (and primes 2, 3: R3.7) | modular, projective |
| PROD-CAL | point evaluation at the exact example | `gb/prod/pointcheck.py` | only-d2 and only-d3a systems vanish identically at the point | exact check |
| RA4 | (PROD) stratum r_a = 4 in an affine chart (evidence only, not projective) | `gb/ra4/ra4gen.py`, `gb/runlog.sh` | see NOTES R3.8 | modular evidence |

## Round 4 (summary; details in NOTES R4.x)
| id | what | command (cwd ncol/) | result | label |
|---|---|---|---|---|
| PAIRS | pair scheme Y (lines W_a, W_b on {e_3 = 0}, B(W_a, W_b) = 0), 3 S5 x Z2 orbit charts of Gr(2,5)^2 | `gb/pairs/pairgen.py P 2 DIR reps.txt`; `gb/runlog.sh`; `gb/pairs/gbcount.py` | 0-dim, degrees 864 / 828 / 792 at P1 | modular, projective |
| PAIRS-NUM | numerical points of Y, defect dimension | `pairs_num.py`, `pairs_classify.py` (`pairs_general.npy`) | chart 01_01: 745 general pairs all e = 4; 30 same-node pairs e = 3 | numerical |
| CC34 | no column-centred 3x4 level 4-space | `gb/cc34/cc34gen.py` (6 orbit charts of Gr(4,8)) | UNIT 6/6 at 3 primes; D = 3 generator vanishes at explicit 3-space (calibration) | modular, projective |
| E3-EXACT | exact "e <= 3" classification on Y | `gb/pairs/` E = 3 systems | msolve segfault at 2 GB (R4.13) | -- |

## Round 5
| id | what | command (cwd ncol/gb/pairs/) | result | label |
|---|---|---|---|---|
| LOC0 / LOCP | local length of Y at a same-node point | `loc/loc0.sing` (Q(i)), `loc/locp.sing` (p = 2147483629) | 6 and 6 | exact |
| KER | kernel-vector systems J_k (rank M <= 3, h-charts) | `kergen.py P PA PB 7 HK ...`; `../runlog.sh ker 900 ker.log` | chart 01_23 h0 segfault at 2 GB (322 s); abandoned | -- |
| LOCJ | local length of J_k at same-node points | `locJ/mklocJ.py` | 2 at all 18 points | exact (mod p) |
| P65 | pair GBs at p = 65521 | `pairgen.py 65521 2 p65 reps.txt`; `../runlog.sh p65 900 p65.log` | NONUNIT, 864 / 828 / 792 standard monomials (74 s, 68 s, 89 s) | modular |
| LOC3 | local lengths at p = 65521 of Y and Y + det M (seed 7), 18 same-node points | `mkloc3.py 65521 {01_01,01_02} 7 loc3`; Singular ds | Y: 6 (18/18); Y + det: 2 (18/18) (`loc3.log`) | exact (mod p) |
| QDET | length of Y_p + det M per chart: msolve GB loaded as Singular SB, entries of M reduced, det by reduced Laplace expansion, vdim(std(G + det)) | `mkq.py 65521 PA PB 7 p65/pair_PA_PB.out sing/q_PA_PB.sing`; `Singular -q` | 01_02: 12 (= 6 x 2); 01_23: 0 (unit); 01_01: see below | modular, exact |
| MM | same length via multiplication matrices (independent check for 01_01) | `mkmm.py sing/q_01_01.sing mm/mm_01_01.sing mm/c0101`; `lenmm.py mm/c0101 65521` (asserts commutativity of the M_v and of mult-by-det) | see below | modular, exact |
| PINT | P-internal R3.2 conditions at the CC34 calibration 3-space | `../../r32/pint.py` | satisfied (1e-13) for m' = (-1 +- i sqrt 2, 1, 1) | numerical (+ exact hand check) |
| MM-CAL | lenmm.py on toy algebras F_p[x]/(x^6-1) (12-variable ring) | `gb/pairs/mmtest/t.sing` + `lenmm.py mmtest/c 65521` | D = x-1: 1, x^3-1: 3, x^2+y: 0 -- all equal to Singular vdim(std(G+D)) | calibration |
| QDET-0101 | chart 01_01 by both methods | `Singular -q sing/q_01_01.sing`; `lenmm.py mm/c0101 65521` | 24 and 24 (rank 840 of 864; commutativity asserts passed) | modular, exact |

## Round 6
| id | what | command (cwd ncol/r32/) | result | label |
|---|---|---|---|---|
| MM-0102 / MM-0123 | multiplication-matrix cross-checks of charts 01_02 / 01_23 (export link kept open) | `../gb/pairs/mm/mm_01_0{2,3}.sing`; `lenmm.py mm/c010{2,3}` | 01_02: 12 (rank 816 of 828); 01_23: 0 (rank 792 of 792) | modular, exact |
| R32-CAL-PT | R_4-only subsystem at the CC34 calibration space, m' = (-1 +- i sqrt 2, 1, 1); negative controls | `r32gen.py 65521 016 2 cal/test.ms r4only`; `evalpt.py` | 34/34 vanish; controls fail (2-6 eqs) | exact point check |
| R32-CAL-NV | same generator, L'' 3-dim / 2-dim (pivots 01, 04, 08, 0) | `r32gen.py 65521 S J calv/...`; `../gb/runlog.sh calv 120 calv.log` | NONUNIT 8/8 run (37, 71, 47, 51, 88, 88, 514, 413) | calibration |
| R32-ONE | one-zero R3.2 closure system, 8 orbit charts x 4 m'-charts, 26 unknowns | `r32gen.py 65521 S J full/c{S}_J{J}.ms`; `../gb/runlog.sh full 900 full.log` | UNIT 32/32 (0.4 - 83 s) | modular, projective |
| R32-TWO | two-zero split isotropic (5,1), m = (1,w,w^2,0,0), Gr(4,13), 82 orbit charts, 36 unknowns | `r32z.py 65521 S zfull/z_S.ms`; `../gb/runlog.sh zfull 600 zfull.log`; staged refinement `stage.sh {none,one,dd} zref{N,A,B} ...` + runlog | 47 UNIT plain + 6 + 22 + 7 UNIT refined = 82/82; calibration zcal: z_1_3_8 NONUNIT(36); zcal2: z_0 NONUNIT(103) | modular, projective |
| R32-G411 | one-zero WITHOUT CC34 input: L'' in Gr(4,11), 13 orbit charts x 4 m'-charts, 31 unknowns | `r32g411.py 65521 S J g411/...`; `../gb/runlog.sh g411 600 g411.log`; `KZ={1,2,3} stage411.sh gz{1,2,3} ...` | 24 UNIT plain + 12 + 12 + 4 refined = 52/52 | modular, projective |
| SX | independent Singular std checks of msolve UNIT verdicts | `ms2sing.py`, `sx/*.sing` | UNIT on z_0_1, z_3_4_5_6, z_6_7_11_12, refined z_1_2_3_4 (c016_J2 stopped at 0.8 GB, memory rule) | exact (mod p) |
| LM2Z [WITHDRAWN R8.4: under-sampled] | numerical probe, two-zero split isotropic spaces (ncol/r32/num/lm2z.py SEED NSTARTS DIM) | `lm2z.py 1 6 3`, `lm2z.py 2 6 4` | dim 3 (L' dim 4): exact solutions (1e-26) in 4/6 starts; dim 4: residual >= 1.000 in 6/6 starts | numerical |

## Round 7
| id | what | command (cwd ncol/r7/) | result | label |
|---|---|---|---|---|
| K3-CENSUS | 3-dim column-centred 3x5 level spaces with defect <= 1 (LM) | `../cc3_search.py 3 1 s0 s1 tmax` (k3/) ; `k3an.py`, `k3exact.py` | 6 hits, all K'(p,q;s1,s2) = (C(e_p-e_q),0) (+) (0,span(e_s1,e_s2)) or mirror, m = e_p - e_q | numerical |
| K3-TAN | local dimension at the hits | `k3tan.py 7 18 20` | Jacobian full rank 24 (isolated, reduced) | numerical |
| K3-KNOWN | the 60 exact points in the chart systems | `k3known.py 65521 S J kfull/...` | all equations vanish; Jacobian rank 24 mod p; per chart 017: 0,0,2,1,1, 015/012: 0 | exact (mod p) |
| K3-EXACT | 0-dim classification systems (3 orbit charts x 5 m-charts, 24 unknowns) | `k3gen.py 65521 S J kfull/...`; `../gb/runlog.sh kfull 600 kfull.log` | 015_J0 UNIT; all others segfault at 2 GB (stopped) | -- |
| LM211 [WITHDRAWN R8.4: under-sampled] | numerical probe K' (+) e_0 U_0 | `num/lm211.py SEED N` | solvable (residual 3e-27) | numerical |
| R211-COND | R2.11 given K': affine system (21 unknowns), 3 x 5 charts | `r211gen.py 65521 UC D r211/...`; `../gb/runlog.sh r211 600 r211.log` | UNIT 15/15; calibration: mode noYZ NEQ 0, noZ NONUNIT 15/15, noY UNIT 3/3 | modular evidence (affine, conditional) |
| R211-L6 | (L6) projective: U_0 (3 charts) x Z in P^8 (9 charts), 10 unknowns | `r211L6.py 65521 UC ZC l6/...`; `../gb/runlog.sh l6 300 l6.log` | UNIT 27/27; lam = 1 chart = noY system | modular, projective (conditional on K') |
| R211-L6-P2 | (L6) at p = 2147483629; Singular check at 65521 | `r211L6.py 2147483629 ...`; `ms2sing.py` | UNIT 27/27; Singular UNIT 3/3 | modular |
| K3-JAC0 | char-0 Jacobian rank at known K' points (rational points, integer system) | `k3jac0.py 0,1,7 2` | 25 of 25 | exact (Q) |

## Round 8
| id | what | command (cwd ncol/r7/) | result | label |
|---|---|---|---|---|
| L6G | general-Z system: U_0 (3 charts) x Z in P^12 (13 charts), 14 unknowns | `r211G.py 65521 UC ZC l6g/...`; `../gb/runlog.sh l6g 300 l6g.log`; `gb2dim.py` | 34 UNIT, 5 charts with ONE reduced point (vdim 1, linear GB) = 3 global points, lam = 0 | modular, projective |
| L6G-P2 | same at p = 2147483629 | `l6gp2/`, `l6gp2.log` | identical pattern | modular |
| L6G-JAC0 | char-0 Jacobian at the 3 points (system over Q(w)) | `l6gjac0.py UC ZC "pt"` | rank 14 = full, equations vanish | exact (Q(w)) |
| K2-CENSUS | 2-dim zero-row column-centred, e <= 1 | `../r8/k2/`, `../cc3_search.py 2 1 ...` | 5 hits, not rigid (products and non-products) | numerical |
| KRED | K' charts with reduced generators | `k3gen.py ... red`, `kred.log` | still segfault at 2 GB | -- |
| LMH-NS80 | properly sampled H probe (NS = 80): dim-4 ker c, types a3 / b22 / b23; dim-3 calibration | `../r8/num/lmH.py TYPE SEED N DK` (NS env), `chkH.py` | dim 4: a3 4/4, b22 2/2, b23 2/2 stall (>= 1); dim 3 (a3): 3.8e-25, fresh-point check 2.3e-24 | numerical |
| H-A3-T2 | H-conjecture, a3, C = V_012 + V_34 (37 -> 36 unknowns), 74 orbit charts, staged by s-pivots | `../r8/hgen.py 65521 S 2 ...`; `hstage.sh`, `hstage2.sh`; logs hs3, hs2, hs2b, hs1t2, hs0t2 | UNIT 74/74 (2 + 19 + 31 + 22) | modular, projective |
| H-CAL | exact point check of the 3-dim T2 system at K'(3,4;0,1) + e_0 V_012 | `../r8/hcal/pt.ms`, `evalpt.py` | 126/126 vanish; perturbations break 8-10 | exact |
| H-A3-T0 | generic C, fixed-point staged refinement | `../r8/hiter.sh 0 3` (local, 28 min cap); big slot `hiter2.sh` (NCOL-HCONJ-A3T0) | partial (stage-4 plain: 3 UNIT of 9 tried; pass 1 running) | modular |
| H-B | types b22 / b23 generators and orbits | `../r8/hgen2.py`, `orbh2.py` (158 / 241 reps), `hiter3.sh` | queued (NCOL-HCONJ-B) | -- |

## Round 9
| id | what | command (cwd ncol/r9/) | result | label |
|---|---|---|---|---|
| D2CHK | second-order identity of D_0(Y)u vs direct perm expansion, on the verified 3-dim H solution | `delta2chk.py`, `a3ident.py`, `a3case.py` | formula 2.7e-13; u.R, (I1), (I2) hold to 1e-13; solution has a, b constant on {0,1,2} | numerical check of exact identities |
| RSS-RUNNER | msolve runner with a RESIDENT cap (watchdog) + 2 GB virtual | `../gb/runlog_rss.sh DIR T LOG` (env RSSKB, ULIM) | msolve needs >= 1.2 GB VIRTUAL to start; RSS stays ~0.2 GB at 1.3 GB VM | tool |
| HC-SPLIT | (I2) parameter families FA/FB on a hard T0 chart | `hc/`, `hc.log` | over the 0.5 GB resident cap in ~10 s | -- |
| HCOLL | collapsed case (3 equal columns) samples | `hcoll/`, `hcoll.log` | 3 UNIT (5-25 s, <= 0.48 GB), 1 over cap | modular |
| HE | E1 / E2 of the closed cover on all 74 T0 orbit charts | `hE/`, `hE.log` | UNIT 148/148 (instant, <= 4 MB) | modular |
| HCS / HCR | plain COLL_{jj'}, E3, refined CA/CB samples | `hcs.log`, `hcr.log` | E3 2/3 UNIT; COLL / CA / CB over the 0.5 GB cap | -- |
| HCP | exact point check of the E3 / COLL01 systems at K'(3,4;0,1) (family T2) | `hcp/` | E3: 132/132 vanish; COLL01: 1 equation fails (as it must) | exact |
| K0FIX | K_0-fixed admissible-Y systems, type a3 (3 SL_3 pair types x {T0, T2} x 11 charts, 11 unknowns) | `k0gen.py 65521 a b c d TC ZC k0s/...`; `../gb/runlog_rss.sh k0s 60 k0s.log` | 64 UNIT + 2 charts with one point each (finite); <= 5 MB, 0.3 s | modular, projective |
| K0-LM | 2-dim zero-row spaces with fixed defect line (well sampled) | `k0/lmk0.py SEED N MODE` | e = 1 found for m = e_2-e_3 (2/4); only e = 0 for generic m (4/4), (x,x,x,y,z) (3/3), (x,x,y,y,z) (2/2) | numerical |
| K2FIX | exact 2-dim zero-row system with m = (1,1,1,7,-10) fixed, 11 orbit charts | `k2fix.py 65521 S 0 k2f/... 7`; `k2f.log` | charts without SL_3 points exceed 0.5 GB (no verdict) | -- |

## Round 10
| id | what | command (cwd ncol/r10/) | result | label |
|---|---|---|---|---|
| K0-BPF | K0, base-point-free normal form (24 unknowns), GB over Q and mod 65521 | `k0bpf.py CHAR 0 1 t.sing gb` | out of memory at 0.5 GB (both) | -- |
| K0-B22 | b22 K_0-fixed admissible-Y systems (6 SL_3 types x {T0,T2} x 11 charts) | `k0gen2.py b22 65521 a b c d TC ZC k0b22/...`; `../gb/runlog_rss.sh k0b22 60 k0b22.log` | 128 UNIT + 4 charts with only Y = x e_4^T (finite for every C); < 5 MB | modular, projective |
| K0-20 | K0 sub-case (2,0) by minimal primes | `k0_20.sing` (Q), `k0_20p.sing` (mod 32003) | Q: out of memory at 0.5 GB; mod p: see NOTES | -- / modular |
| K0-11 | K0 sub-case (1,1) by minimal primes over Q | `k0_11.sing` (with m), `k0_11b.sing` (rank <= 1 minors, no m) | see NOTES | exact (Q) |
| SL2 | strongly level 2-dim zero-row spaces, 3 orbit charts of Gr(2,10), mod 65521 | `slgen.py`, `sl/`, `sl.log`; decompositions in Singular | NONUNIT, Krull dim 1: rigid pairs + families F1, F2 | modular |
| SLQ | exact classification over Q of the q = 1 and mixed q = 2 cases | `slq1.sing`, `slq2.sing` | q=1: only F2[1:0], F1[1:1]; q=2 two reflections: F2; three reflections: UNIT | exact (Q, Q(w)) |
| KFAM | K_0-family systems a3 / b22 | `kfam.py TYPE 65521 FAM a b HC TC ZC ...`; `kfa3.log`, `kfb22.log`; fibre check `fib/`, `fibb22/` | a3 248 UNIT + 60 finite; b22 520 UNIT + 52 finite | modular, projective |

## Round 11
| id | what | command (cwd ncol/) | result | label |
|---|---|---|---|---|
| K0Q | K0 over Q, 20 jobs (driver) | `r11/runK0Q.sh` (ULIM, JT, CH); generators `r11/k0q.py`, `r11/k0q_11.py` | queued NCOLK0Q; local mod-p triage over 0.5 GB | -- |
| B22T2 | b22 family T2 staged, RSS-capped | `r8/hiter3rss.sh b22 2 6` (CT 30) | 8 UNIT / 30 RSSCAP / 1 TIMEOUT before stop; queued NCOLHB22T2 | -- |
| KFB23 | b23 K_0 families F1 (13) / F2 (7) | `r10/kfam.py b23 ...`, `r10/kfb23.log`, `r10/fibb23.log` | 630 UNIT + 250 NONUNIT, fibres finite 250/250 | modular, projective |
| K0B23 | b23 rigid pairs (9 types) | `r10/k0gen2.py b23 ...`, `r10/k0b23.log`, `r10/fibk0b23.log` | 182 UNIT + 16 finite (14 fibre-checked, 2 single points) | modular, projective |
| CEX | K0 counterexample + family shapes | `r11/cex/cex1.py`, `famchk2.sing`, `cexS4.sing`, `cexN.sing` | K0 false; members F/S4/N exact | exact |
| K0R11 | restricted (1,1) census mod 32003 | `r11/runK0R_local.sh` (CH=32003), `r11/k0r.py` | 36/36 charts 0-dim, counts = F + S4 + N | modular (triage) |
| KFIX | K_0-fixed systems, 15 members + calibration | `r11/k0gen3.py`, `r11/runkfix.sh`, `r11/kfix.log` | 330/330 UNIT; calibration (01|23) 1 point at tp=-3 | modular 65521, projective |
| CASE11 | (1,1) case split B1 / C over Q | `r11/k0_11case.py`, `r11/case11/` | B1: a3 only N-type, b22 none; C: running | exact |
| C3 | (1,1) Case C, factorised split, over Q | `r11/k0_11C3.py`, `r11/runC3.sh`, `r11/C3.log` | b22: 6 S4 points; a3: 12 S4 points; rest UNIT | exact |
| RS | r_a = 2 charts with same/crossed split, mod p | `r11/k0rs.py` | 2/2 over 0.5 GB (halt 14) | -- |
