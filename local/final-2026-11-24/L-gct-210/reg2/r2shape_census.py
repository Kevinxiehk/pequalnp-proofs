# Round 11, target 2: shape of the genuine 2-dim skew blocks in the census.  For a row piece (r,j) [resp. column piece (a,b)] whose sum-zero part
# P_0 has X_0 = 2-dim with no line elements in row r, write y = B x and split B x = (component in X_0) + phi(x) (component in X_0^perp cap 1^perp),
# modulo the y-parts Lambda_j of row-j line elements.  phi = 0 (mod Lambda_j) <=> the block is a PURE skew deformation t J_X0 (the deformation table).
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
from ext6 import F45
src=open('/home/kevxhk/work/L-gct-210/reg2/bispan_all.py').read(); files=eval(src.split('files=')[1].split('\n')[0])+sorted(glob.glob('dr35_u*_s*.npy'))
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj()
out=[]
for f in files:
    try: M=np.load(f)
    except Exception: continue
    if M.ndim!=3 or M.shape[1:]!=(4,5) or np.linalg.matrix_rank(M.reshape(len(M),-1),tol=1e-8)!=6: continue
    M=M/np.abs(M).max()
    for kind in ('R','C'):
        n=4 if kind=='R' else 5
        for a in range(n):
            for b in range(n):
                if a==b: continue
                m=np.zeros((4,5),bool)
                if kind=='R': m[a]=True; m[b]=True
                else: m[:,a]=True; m[:,b]=True
                P=sub_supported(M,m)
                if len(P)<2: continue
                X=(P[:,a,:] if kind=='R' else P[:,:,a]); Y=(P[:,b,:] if kind=='R' else P[:,:,b])
                s=X.sum(1)
                c0=null(s[None,:],1e-6) if np.abs(s).max()>1e-6 else np.eye(len(P))
                X0=c0@X; Y0=c0@Y
                if np.linalg.matrix_rank(X0,tol=1e-6)!=2 or len(X0)!=2: continue      # exactly a 2-dim X_0, no row-b line elements in P_0
                # line elements of row/col a inside P_0 would make len(X0) > rank; excluded above.  Lambda_b: single-row (col) elements of b
                mb=np.zeros((4,5),bool)
                if kind=='R': mb[b]=True
                else: mb[:,b]=True
                Lb=sub_supported(M,mb); Lam=(Lb[:,b,:] if kind=='R' else Lb[:,:,b]) if len(Lb) else np.zeros((0,X0.shape[1]))
                dim=X0.shape[1]
                comp=null(np.concatenate([X0,np.ones((1,dim))],0).conj(),1e-9).conj()      # basis of X_0^perp cap 1^perp (bilinear)
                if len(comp)==0: continue
                # phi = projection of Y0 onto comp along X_0 + C1 (+ Lambda_b)
                Bas=np.concatenate([X0,np.ones((1,dim)),Lam,comp],0)
                coef=np.linalg.lstsq(Bas.T,Y0.T,rcond=None)[0].T
                phi=coef[:,-len(comp):]
                # remove the part of phi explained by Lambda_b (already in the basis) -> phi is the residual component
                out.append((np.abs(phi).max()/max(1e-12,np.abs(Y0).max()),f,kind,a,b,len(Lam)))
print('2-dim blocks found:',len(out))
big=[o for o in out if o[0]>1e-6]; print('with phi != 0 (relative > 1e-6):',len(big))
for o in sorted(big,reverse=True)[:12]: print('   |phi|/|y| = %.2e  %s %s(%d,%d) Lambda_b dim %d'%o)
print('pure skew (phi = 0):',len(out)-len(big))
