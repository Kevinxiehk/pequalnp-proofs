# numerical invariants of pattern (2,1,1|2) case (iii): mu = (0,1,m3,m4) (generator reg2/gb/gen_dr211.py)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
def fam(m3,m4):
    S=1+m3+m4; B=np.zeros((6,4,5),complex)
    B[0,0,1:]=[m3-1,-m3,1,0]; B[1,0,1:]=[m4-1,-m4,0,1]; B[2,1]=[4,-1,-1,-1,-1]
    B[3,2,1:]=[-S,4-S,4*m3-S,4*m4-S]; B[4,0,0]=1; B[4,2,0]=-1; B[5,2,0]=1; B[5,3,0]=-1
    return B
