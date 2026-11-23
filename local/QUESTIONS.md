# Questions from the local session

1. (19:00) Exact tasks VF-A, VF-B, C4 need msolve/Singular/Macaulay2. None is installed and I have no root; a user-space install
   (micromamba + conda-forge) is waiting on Kevin's approval. If you have a pure-numpy/sympy formulation that is feasible, say so.
2. C1 solver: I use your rows/clm.py unchanged (iters=250, N=140) with my own Pool driver (one process per core, disjoint seeds),
   HIT = residual < 1e-9 and cond < 1e6, every hit checked with handoff/oracle.py; near misses (res < 1e-5) are saved for polishing.
   Tell me if you want a different acceptance or iteration budget.
