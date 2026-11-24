# Round 11, target 2 (better conditioned): for the genuine R2/C2 blocks of the mechanism census (piece with g2,skew2), with no line element of
# the first row/column in P_0 and X_0 2-dim NONDEGENERATE: phi = y - proj_{X_0}(y) - mean(y) 1 reduced modulo Lambda_b; report |phi| / |y|.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, re
from pieces import sub_supported
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj()
cases=[]
for line in open('/home/kevxhk/work/L-gct-210/reg2/evidence/logs/r11_mech_census.log'):
    if 'g2,skew2' in line:
        f=line.split('e.g. ')[1].split()[0]
        for m in re.finditer(r'([RC])(\d)(\d):g2,skew2',line): cases.append((f,m.group(1),int(m.group(2)),int(m.group(3))))
# also test every space of the census with such pieces (not just the example): re-scan all files listed in mech_census examples only
for f,kind,a,b in cases:
    M=np.load(f); M=M/np.abs(M).max()
    for (p,q) in ((a,b),(b,a)):
        m=np.zeros((4,5),bool)
        if kind=='R': m[p]=True; m[q]=True
        else: m[:,p]=True; m[:,q]=True
        P=sub_supported(M,m); X=(P[:,p,:] if kind=='R' else P[:,:,p]); Y=(P[:,q,:] if kind=='R' else P[:,:,q])
        s=X.sum(1); c0=null(s[None,:],1e-6) if np.abs(s).max()>1e-6 else np.eye(len(P)); X0=c0@X; Y0=c0@Y
        # remove row/col-q line elements (x = 0) and row/col-p line elements (y = 0)
        ux,sx,vx=np.linalg.svd(X0); rx=int((sx>1e-6).sum())
        if rx!=2: print('  %s %s(%d->%d): dim X0 = %d (skip)'%(f,kind,p,q,rx)); continue
        # keep the part of P_0 where x runs over X0 with a section y(x): solve least squares for coefficients giving x = basis
        Xb=vx[:2]                                   # basis of X0 (rows)
        Cf=np.linalg.lstsq(X0.T,Xb.T,rcond=None)[0].T  # combos of P_0 rows with x = Xb
        Yb=Cf@Y0
        mq=np.zeros((4,5),bool)
        if kind=='R': mq[q]=True
        else: mq[:,q]=True
        Lq=sub_supported(M,mq); Lam=(Lq[:,q,:] if kind=='R' else Lq[:,:,q]) if len(Lq) else np.zeros((0,X0.shape[1]))
        G=Xb@Xb.T
        if abs(np.linalg.det(G))<1e-6*np.abs(G).max()**2: print('  %s %s(%d->%d): X0 DEGENERATE (det G ~ %.1e)'%(f,kind,p,q,abs(np.linalg.det(G)))); continue
        proj=(Yb@Xb.T)@np.linalg.solve(G,Xb)       # bilinear projection onto X0
        phi=Yb-proj-Yb.mean(1)[:,None]
        if len(Lam):
            co=np.linalg.lstsq(Lam.T,phi.T,rcond=None)[0]; phi=phi-(Lam.T@co).T
        J=np.linalg.lstsq(Xb.T,proj.T,rcond=None)[0].T     # matrix of the X0-component: should be t * J (skew w.r.t. G)
        sk=J@G; print('  %s %s(%d->%d): |phi|/|y| = %.1e   X0-part skew? |JG + (JG)^T| = %.1e  Lambda dim %d'%(f,kind,p,q,np.abs(phi).max()/np.abs(Yb).max(),np.abs(sk+sk.T).max(),len(Lam)))
