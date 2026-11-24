# Round 11: probe the two-row pieces of numerically given level spaces: for rows (r,j): P = M cap {rows r,j}, P_0 = P cap {S x = 0},
# X_0 = row-r projection of P_0, line elements, and (when defined) the map B: x -> y and its rank.  Input: the doubly deformed conic family
# (built as in gb/num_double.py) or .npy files.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
from ext6 import F45
def null(A,tol=1e-8):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0] if len(s) else 1)).sum()); return vh[r:].conj()
def probe(M,name):
    M=M/np.abs(M).max()
    rg=np.random.default_rng(0); C=rg.normal(size=(30,len(M)))+1j*rg.normal(size=(30,len(M)))
    lev=np.abs(F45(np.einsum('nk,kij->nij',C,M))-120).max()
    out=[]
    for r in range(4):
        for j in range(4):
            if r==j: continue
            mask=np.zeros((4,5),bool); mask[r]=True; mask[j]=True
            P=sub_supported(M,mask)
            if len(P)==0: continue
            X=P[:,r,:]; Y=P[:,j,:]
            # P_0 = {S x = 0}
            c0=null(X.sum(1)[None,:]) if len(P)>1 else np.zeros((0,len(P)))
            P0=np.einsum('kc,cab->kab',c0,P) if len(c0) else np.zeros((0,4,5))
            X0=P0[:,r,:]; Y0=P0[:,j,:]
            dX=np.linalg.matrix_rank(X0,tol=1e-7) if len(P0) else 0
            lj=len(P0)-dX                                  # elements of P_0 with x = 0: single-row elements in row j
            # single-row elements in row r inside P_0 (y = 0)
            dY=np.linalg.matrix_rank(Y0,tol=1e-7) if len(P0) else 0
            lr=len(P0)-dY
            if dX>=2: out.append('rows (%d,%d): dim P=%d dim P0=%d dim X0=%d  line elems: row %d: %d, row %d: %d  => rank B = dim Y0 - (line_j) = %d'%(r,j,len(P),len(P0),dX,r,lr,j,lj,dY-lj if lj==0 else -1))
    print(name,'level err %.1e dim %d'%(lev,np.linalg.matrix_rank(M.reshape(len(M),-1),tol=1e-8)))
    for o in out: print('   ',o)
    if not out: print('    (no two-row piece with dim X0 >= 2)')
if __name__=='__main__':
    for f in sys.argv[1:]: probe(np.load(f),f)
