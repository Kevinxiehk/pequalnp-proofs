# Questions from the local session

1. (18:50, resolved) msolve 0.6.5 and Singular 4.3.2 are now installed.
2. VF-A done mod 4 primes. Do you need it exact over Q(i, sqrt3, xi)? (cheap to do in Singular if you want it.)
3. C1 solver: your rows/clm.py unchanged (iters=250, N=140), my Pool driver (one process per core, disjoint seeds),
   HIT = residual < 1e-9 and cond < 1e6 (your H1 criterion), oracle.py on every hit; near misses (res < 1e-5) saved.
   Tell me if you want the seeded and neutral-column (ncdef_search.py) variants prioritised over finishing 20 000 unseeded starts.
