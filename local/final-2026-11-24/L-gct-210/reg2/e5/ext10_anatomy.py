# Round 19: anatomy of the census e = 5 spaces: line parts, genuine element (rank one?), and a numerical check of the hand formulas.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
from a5 import onb
np.set_printoptions(precision=4,suppress=True,linewidth=170)
for nm,PQ in (('ext_10',(0,2)),('ext_9',None),('ext_11',None),('dr35_u2_s52_400',(2,3)),('dr35_u3_s41_116',(1,2)),('dr35_u3_s41_29',(1,3))):
    P,Q=PQ if PQ else (None,None)
    M=onb(np.array(np.load('/home/kevxhk/work/L-gct-210/reg2/%s.npy'%nm),complex))
    U=[];W=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; U.append(sub_supported(M,m))
    for c in range(5):
        m=np.zeros((4,5),bool); m[:,c]=True; W.append(sub_supported(M,m))
    srow=[len(u) for u in U]; scol=[len(w) for w in W]
    free=[i for i in range(4) if srow[i]==0]
    if P is None: P,Q=free[0],free[1]
    m=np.zeros((4,5),bool); m[P]=True; m[Q]=True; Pp=sub_supported(M,m)
    Lin=np.concatenate([l.reshape(len(l),-1) for l in U+W if len(l)],0)
    Qo=np.linalg.qr(Lin.T)[0]; Pf=Pp.reshape(len(Pp),-1); Gp=Pf-(Pf@Qo.conj())@Qo.T; u_,s_,vh=np.linalg.svd(Gp); g=vh[0]
    c=np.linalg.lstsq(Pf.T,g,rcond=None)[0]; E=(c@Pf).reshape(4,5); x,y=E[P],E[Q]; z=x+y
    Uo=[U[k][i][k] for k in range(4) if k not in (P,Q) for i in range(len(U[k]))]
    dimUo=np.linalg.matrix_rank(np.array(Uo),tol=1e-8) if Uo else 0
    print('%-16s srow %s scol %s pair %s  dim U_other=%d  |z|/|x| = %.1e  s = %.1e  <x,x> = %.1e'%(nm,srow,scol,(P,Q),dimUo,np.linalg.norm(z)/np.linalg.norm(x),abs(x.sum()),abs(x@x)))
    for cc in range(5):
        for v in W[cc]:
            vv=v[:,cc]; print('     col %d line v = %s   (v_P, v_Q) = %s'%(cc,np.round(vv/np.abs(vv).max(),4),np.round(vv[[P,Q]]/np.abs(vv).max(),4)))
    for k in range(4):
        for u in U[k]: print('     row %d line u = %s'%(k,np.round(u[k]/np.abs(u[k]).max(),4)))
    print('     x =',np.round(x/np.abs(x).max(),4))
