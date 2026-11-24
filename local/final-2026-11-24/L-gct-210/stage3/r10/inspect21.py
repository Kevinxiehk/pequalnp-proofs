import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); from t1_c52 import rank, single_rows
np.set_printoptions(precision=3,suppress=True,linewidth=150)
Z=np.load(sys.argv[1]); d=len(Z)
def ker(rows): 
    A=np.array([[Z[k][i,j] for k in range(d)] for i in rows for j in range(5)]); u,s,vh=np.linalg.svd(A.T if False else A); 
    r=int((s>1e-6*s[0]).sum()); return d-r
print('single-row dims',single_rows(Z),' 2-row dims m_kl',{(k,l):ker([i for i in range(4) if i not in (k,l)]) for k,l in itertools.combinations(range(4),2)})
for r in range(4):
    u,s,vh=np.linalg.svd(Z[:,r,:]); P=vh[:2]
    # normalise the plane basis: reduced row echelon form
    piv=np.argsort(-np.abs(P).max(axis=0))[:2]; piv.sort(); R=np.linalg.solve(P[:,piv],P)
    print('row',r,'plane RREF on pivots',piv,'\n',R)
# single-row vectors
for r in range(4):
    A=np.array([[Z[k][i,j] for k in range(d)] for i in range(4) if i!=r for j in range(5)])
    u,s,vh=np.linalg.svd(A); rk=int((s>1e-6*s[0]).sum()); N=vh[rk:].conj()
    for c in N:
        w=np.tensordot(c,Z,axes=1)[r]; w=w/w[np.argmax(np.abs(w))]; print('single-row vector in row',r,':',w,' sum %.1e <w,w> %.2e'%(abs(w.sum()),abs(w@w)))
