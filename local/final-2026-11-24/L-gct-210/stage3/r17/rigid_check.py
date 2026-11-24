# Round 17: rigid member of the (1,1,1,1,0) "three m + w" configuration: m = (1, i, -1, -i, 0) on rows 0,1,2, w = (1,1,1,1,-4) on row 3;
# is the span with the FULL free column on rows {0,1,2,4} in column 4 level?  (If yes, L contains a free column on four rows -> PFC.)
import sympy as sp, itertools
I=sp.I; c0,c1,c2,c3,C0,C1,C2=sp.symbols('c0 c1 c2 c3 C0 C1 C2'); C4=-C0-C1-C2
m=[1,I,-1,-I,0]; w=[1,1,1,1,-4]
X=sp.zeros(5,5)
for j in range(5):
    X[0,j]=c0*m[j]; X[1,j]=c1*m[j]; X[2,j]=c2*m[j]; X[3,j]=c3*w[j]
X[0,4]+=C0; X[1,4]+=C1; X[2,4]+=C2; X[4,4]+=C4
def sig(M,t):
    tot=0
    for R in itertools.combinations(range(5),t):
        for C in itertools.combinations(range(5),t):
            tot+=sp.Matrix(M.extract(list(R),list(C))).per()
    return sp.expand(tot)
for t in range(1,6): print('sigma_%d ='%t, sp.factor(sig(X,t)))
