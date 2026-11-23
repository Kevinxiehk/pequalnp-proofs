import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2')
from fractions import Fraction as Fr
import exact_fo2 as ef
def fam22(m3,m4):
    S=1+m3+m4; E=ef.E
    return [E([(0,1,m3-1),(0,2,-m3),(0,3,1)]),E([(0,1,m4-1),(0,2,-m4),(0,4,1)]),E([(1,0,4),(1,1,-1),(1,2,-1),(1,3,-1),(1,4,-1)]),
            E([(1,0,-S),(1,1,-S),(1,2,5-S),(1,3,5*m3-S),(1,4,5*m4-S)]),E([(0,0,1),(2,0,-1)]),E([(2,0,1),(3,0,-1)])]
for (m3,m4) in ((0,0),(0,1),(1,0),(1,1),(2,3)):
    ef.cert(fam22(m3,m4),'DR22 mu=(0,1,%d,%d)'%(m3,m4))
