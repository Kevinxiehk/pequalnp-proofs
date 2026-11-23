import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/numerics'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from core import orth, fresh_check, invariants, ext_space, grass_tangent
for f in sys.argv[1:]:
    B=np.load(f)
    print(f, 'fresh', fresh_check(B), invariants(B))
    dE,E,s=ext_space(B); print('  extdim', dE, 'grass tangent', grass_tangent(B)[0])
