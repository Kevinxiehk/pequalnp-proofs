import numpy as np, sys
sys.argv=['x']; exec(open('grad.py').read().split("B=l080()")[0])
def supp_space(cells,sumzero=True):
    E=[]
    for (i,j) in cells:
        t=np.zeros((n,n)); t[i,j]=1; E.append(t.ravel())
    E=np.array(E)
    if sumzero:
        # project onto sum-zero within span
        c=E.sum(1); Bz=np.linalg.svd(c[None,:])[2][1:]  # combos with zero total
        E=Bz@E
    return E.astype(complex)
tests={
 'rows 3,4 (sum-zero total) d=9':[(i,j) for i in (3,4) for j in range(5)],
 'row4+col4 d=8':[(4,j) for j in range(5)]+[(i,4) for i in range(4)],
 '3x3 block d=8':[(i,j) for i in range(2,5) for j in range(2,5)],
 'cols 3,4 + row 4 d=?':[(i,j) for i in range(5) for j in (3,4)]+[(4,j) for j in range(3)],
}
for k,c in tests.items():
    B=supp_space(c); print(k,'dim',B.shape[0],'dim W=',Wdim(B), 'needed for contradiction at this d: >',25-B.shape[0])
