import sys; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""symdc_run.py -- gen_sym_dc.main() with the guarded run_msolve (E-STALE-OUTPUT; round 14).  Same arguments as gen_sym_dc.py:
   python3 -I symdc_run.py P S CHART K OUTDIR [first last] run timeout=T"""
import exactlib as X, exactlib_fixed
X.run_msolve = exactlib_fixed.run_msolve
import gen_sym_dc
assert gen_sym_dc.X.run_msolve is exactlib_fixed.run_msolve
gen_sym_dc.main()
