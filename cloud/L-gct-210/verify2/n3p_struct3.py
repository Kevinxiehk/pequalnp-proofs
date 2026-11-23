import pickle, itertools, numpy as np
from fractions import Fraction as Fr
hard=pickle.load(open('/home/claude/work/L-gct-210/verify2/n3p_hard.pkl','rb'))
P3=list(itertools.permutations(range(3)))
def perm9(b): return sum(b[p[0]]*b[3+p[1]]*b[6+p[2]] for p in P3)
names=['y%d'%k for k in range(4)]
for V,comp,Q in hard:
    print('V_0 basis:',[''.join('%2d'%int(x) for x in v) for v in V])
    print('  complement basis of W:',[''.join('%2d'%int(x) for x in v) for v in comp])
    for i,q in enumerate(Q):
        terms=[]
        for a in range(4):
            for b in range(a,4):
                c=q[a][b]*(1 if a==b else 2)
                if c!=0: terms.append('%s*%s*%s'%(c,names[a],names[b]))
        print('  q%d ='%i,' + '.join(terms) if terms else '0')
    # cubic: coefficients via evaluation at monomials is messy; print perm of generic b = sum y_k comp_k symbolically by expanding
    coef={}
    for p in P3:
        # product of three linear forms
        lf=[[comp[k][c] for k in range(4)] for c in (p[0],3+p[1],6+p[2])]
        for a in range(4):
            for b in range(4):
                for c in range(4):
                    v=lf[0][a]*lf[1][b]*lf[2][c]
                    if v!=0:
                        key=tuple(sorted((a,b,c))); coef[key]=coef.get(key,0)+v
    print('  perm =',' + '.join('%s*%s'%(v,'*'.join(names[k] for k in key)) for key,v in coef.items() if v!=0))
