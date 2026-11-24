import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5'); sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from weight import weight_dc, pi
def stab(B, tol=1e-9):
    B=np.array(B)/np.abs(B).max(); d=len(B); Kf=B.reshape(d,25); Q=np.linalg.qr(Kf.T)[0]; Pperp=np.eye(25)-Q@Q.conj().T
    out=[]
    for side in ('row','col'):
        M=[]
        for e in range(5):
            h=np.zeros((5,5))
            if side=='row': h[e,:]=1
            else: h[:,e]=1
            M.append(np.concatenate([Pperp@pi(h*b).ravel() for b in B]))
        M=np.array(M).T; s=np.linalg.svd(M,compute_uv=False); out.append(5-int((s>tol).sum()))
    return out
if __name__=='__main__':
    from blocksrch import ambient, run as brun
    w=np.exp(2j*np.pi/5); z=np.exp(2j*np.pi/3); chi=lambda k: w**(k*np.arange(5))
    u=np.array([1,z**2,z,0,0]); ub=u.conj()
    cases={'graded 3-row K (level,4)':np.array([np.outer(u,chi(1)),np.outer(u,chi(4)),np.outer(ub,chi(2)),np.outer(ub,chi(3))]),
     'V x v (P234,4)':np.array([np.outer(np.eye(5)[i]-np.eye(5)[4],chi(1)) for i in range(4)]),
     'weight P234 (32,5)':weight_dc([1,2,0,4,3],[1,2,3,4,0],30,[2,3,4,6]),
     'weight P234 (4,5)':weight_dc([1,2,3,0,4],[1,2,3,4,0],20,[1,2,3,4]),
     'weight p2p3 6 (32,5)':weight_dc([1,2,0,4,3],[1,2,3,4,0],30,[2,3,4,6,8,9]),
     'weight p2p3 6 (4,5)':weight_dc([1,2,3,0,4],[1,2,3,4,0],20,[1,2,3,11,12,13]),
     'weight level 3 (32,5)':weight_dc([1,2,0,4,3],[1,2,3,4,0],30,[2,3,4]),
     'weight level 3 (4,5)':weight_dc([1,2,3,0,4],[1,2,3,4,0],20,[1,2,3])}
    f,T,_=brun(ambient([0,1,2]),4,[2,3],15,1,25); cases['generic 3-row K4 (level)']=T
    for f in ['sol_d5_k23_s1.npy','sol_d3_k234_s4.npy','sol_d4_k23_s24.npy']: cases['random LM '+f]=np.load(f)
    for k,B in cases.items(): print('%-34s d=%d  stab dims (row fns, col fns), constants included: %s'%(k,len(B),stab(B)))
