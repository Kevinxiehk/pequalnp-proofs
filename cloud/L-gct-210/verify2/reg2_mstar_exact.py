import importlib.util
from fractions import Fraction as Fr
spec=importlib.util.spec_from_file_location('ex7','/home/claude/work/L-gct-210/rows/exact7.py'); ex7=importlib.util.module_from_spec(spec); spec.loader.exec_module(ex7)
def E(): return [[0]*5 for _ in range(5)]
def Mstar(x,y):
    B=[]
    for w in ([1,-1,-1,1,0],[1,0,0,0,-1],[0,1,1,-2,0]):
        t=E(); t[3]=list(w); B.append(t)
    t=E()
    for i in range(3): t[i][0]=x[i]
    B.append(t); t=E()
    for i in range(3): t[i][3]=y[i]
    B.append(t); t=E(); t[2][1]=1; t[2][2]=-1; B.append(t)
    return B
for x,y in (((1,-1,0),(1,1,-2)),((2,-1,-1),(0,1,-1)),((Fr(1,2),Fr(3,2),-2),(7,-5,-2))):
    assert sum(x)==0 and sum(y)==0 and sum(a*b for a,b in zip(x,y))==0
    const,rest=ex7.level_identity(Mstar(x,y))
    print('M*(%s,%s): perm(J + (Y;0)) = %s + (%d nonzero non-constant coefficients) as a polynomial identity'%(tuple(str(a) for a in x),tuple(str(a) for a in y),const,len(rest)))
