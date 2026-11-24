# Round 16: 3x5 level-space formulas as Singular strings.  For a k x 5 matrix x (rows r_i), sigma_m(x) = sum of all m x m sub-permanents;
# level <=> sigma_1 = .. = sigma_k = 0 on the space.  Deletion vectors: c(x)_j = sigma_1(x minus col j), D_2(x)_j = sigma_2(..), D_3(x)_j = sigma_3(..).
import itertools
def sig(rows, m, cols):
    """sigma_m of the matrix with the given rows (lists of strings) restricted to the column list cols"""
    terms=[]
    for R in itertools.combinations(range(len(rows)),m):
        for C in itertools.permutations(cols,m):
            terms.append('*'.join('(%s)'%rows[R[k]][C[k]] for k in range(m)))
    return '('+'+'.join(terms)+')' if terms else '0'
def level(rows): return [sig(rows,m,range(5)) for m in range(1,len(rows)+1)]
def deletion(rows):
    """c, D_2, D_3 (lists of 5 strings each) for a 3-row matrix"""
    return [[sig(rows,m,[c for c in range(5) if c!=j]) for j in range(5)] for m in (1,2,3)]
if __name__=='__main__':   # numerical self-check of sig against brute force sub-permanents
    import numpy as np
    rg=np.random.default_rng(0); X=rg.normal(size=(3,5))
    rows=[[repr(float(v)) for v in X[i]] for i in range(3)]
    def subperm_sum(M,m):
        tot=0
        for R in itertools.combinations(range(M.shape[0]),m):
            for C in itertools.combinations(range(M.shape[1]),m):
                tot+=sum(np.prod([M[R[k],p[k]] for k in range(m)]) for p in itertools.permutations(C))
        return tot
    for m in (1,2,3): print(m, eval(sig(rows,m,range(5))), subperm_sum(X,m))
