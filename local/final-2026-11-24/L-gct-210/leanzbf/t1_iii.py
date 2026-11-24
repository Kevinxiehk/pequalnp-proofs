import itertools
from fractions import Fraction as F
def perm3(M):
    return sum(M[0][p[0]]*M[1][p[1]]*M[2][p[2]] for p in itertools.permutations(range(3)))
def P(A,B,D):
    return perm3([[A,B,-A-B],[D,-B,-D-B],[D,A+B-D,A+B]])
for pt in [(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1),(1,2,3)]:
    print(pt, P(*map(F,pt)))
# symbolic expansion via sampling: degree 3 in 3 vars -> fit
import random
