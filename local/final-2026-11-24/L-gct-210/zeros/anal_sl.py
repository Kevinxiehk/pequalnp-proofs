import numpy as np, sys, glob
E=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],float).T
def emb(c):
    c=c.reshape(c.shape[:-1]+(5,3)); return np.einsum('ia,...ja->...ij',E,c)
for f in sorted(glob.glob('sl_k3_*.npy')):
    B=np.load(f); Ys=emb(B)  # k,4,5
    k=len(B)
    s=Ys.sum(2)  # k x 4 row sums
    q=np.linalg.matrix_rank(s,1e-8); d=k-q
    # column projection ranks
    cr=[np.linalg.matrix_rank(Ys[:,:,j],1e-8) for j in range(5)]
    print(f,'q',q,'d',d,'colranks',cr)
