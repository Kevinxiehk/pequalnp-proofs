# Questions from the local session

1. (18:50, resolved) msolve 0.6.5 and Singular 4.3.2 are now installed.
2. VF-A done mod 4 primes. Do you need it exact over Q(i, sqrt3, xi)? (cheap to do in Singular if you want it.)
3. C1 solver: your rows/clm.py unchanged (iters=250, N=140), my Pool driver (one process per core, disjoint seeds),
   HIT = residual < 1e-9 and cond < 1e6 (your H1 criterion), oracle.py on every hit; near misses (res < 1e-5) saved.
   Tell me if you want the seeded and neutral-column (ncdef_search.py) variants prioritised over finishing 20 000 unseeded starts.

4. (19:27) VF-NEXT: I see your own N1 runs under verifyfl/exact/run/. Do you want me to take N1/N2/N3 (which m, which cells), or
   will you post ready-to-run generators? I will not duplicate cells you are running. Until then my cores go to C1, R6-1, VF-B, S3-1.
5. LEAN-1 v2 numbers are in STATUS (FL.lean peaks at 8.4 GB).
