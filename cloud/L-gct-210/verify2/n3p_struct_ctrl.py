# verify2: positive control for the exact pipeline of n3p_struct2.py on 3-dim spans (where lineality spaces exist).
import itertools, sys
from fractions import Fraction as Fr
src=open('/home/claude/work/L-gct-210/verify2/n3p_struct2.py').read()
head=src.split("hist={}; hard=[]; cex=[]")[0].replace("spans=pickle.load(open('/home/claude/work/L-gct-210/verify2/n3p_spans.pkl','rb'))","spans=[]")
exec(head)
def analyse(V,b):
    V=[[Fr(x) for x in v] for v in V]; k=len(V)
    lin=[DD(V[i],V[j]) for i in range(k) for j in range(i,k)]
    BV=nullspace(lin,9)
    inBV=all(sum(l[c]*b[c] for c in range(9))==0 for l in lin)
    quad=[D(V[i],b,b) for i in range(k)]
    cubic_on_V=all(perm9([sum(y[i]*V[i][c] for i in range(k)) for c in range(9)])==0 for y in itertools.product(range(4),repeat=k))
    return len(BV),inBV,quad,perm9(b),cubic_on_V
def cell(i,j): return [1 if c==3*i+j else 0 for c in range(9)]
I=[Fr(x) for x in (1,0,0,0,1,0,0,0,1)]; J=[Fr(1)]*9
print('upper triangular, b = I: (dim B_V, b in B_V, quadrics at b, perm(b), perm=0 on V_0) =',analyse([cell(0,1),cell(0,2),cell(1,2)],I))
# 3x3 level space of dim 3 (L080 analogue): e_2 (1,-1,0), (e_0 - e_2) e_2^T, (e_1 - e_2) e_2^T ; b = J
V=[[0,0,0,0,0,0,1,-1,0],[0,0,1,0,0,0,0,0,-1],[0,0,0,0,0,1,0,0,-1]]
print('level 3x3 (dim 3), b = J:',analyse(V,J))
# brute numeric confirmation of the second one
import random
def pm(b): return perm9(b)
ok=all(pm([J[c]+sum(Fr(random.randint(-5,5))*0+0 for _ in range(1)) for c in range(9)])==6 for _ in range(1))
vals=set()
for _ in range(50):
    y=[Fr(random.randint(-5,5)) for _ in range(3)]
    vals.add(pm([J[c]+sum(y[i]*V[i][c] for i in range(3)) for c in range(9)]))
print('perm(J + eta) values on the level space:',vals)
