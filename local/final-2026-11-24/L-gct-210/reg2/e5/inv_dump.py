# Round 18: numerical invariants (level error, e, dim E_0, dim Omega, dim T_1, FO2) of the dumped quadratic-stage survivors.
import sys, glob, os; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from nc_num import report
from t import rowpart, colpart
from a5 import onb
for f in sorted(glob.glob(sys.argv[1] if len(sys.argv)>1 else '/home/kevxhk/work/L-gct-210/reg2/e5/dump/*.npy')):
    B=np.load(f); Bo=onb(np.array(B,complex))
    print(os.path.basename(f),'srow',[len(rowpart(Bo,[i])) for i in range(4)],'scol',[len(colpart(Bo,[j])) for j in range(5)],flush=True)
    report(os.path.basename(f)[:30],B)
