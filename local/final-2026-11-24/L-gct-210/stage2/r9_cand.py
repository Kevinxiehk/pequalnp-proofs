# The D0-4 (pattern M, choice A, case i) point f0 = f3 = 2 found by elimination: build X exactly, check level, (iii), single-row parts,
# and run the T_1 tool (Omega), FO2 and (T2).
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
exec(open('/home/kevxhk/work/L-gct-210/stage2/r6_T2.py').read().split("if __name__=='__main__':")[0])
def mk(cho,f0,f3):
    Z=np.zeros(4); Yb=[(np.ones(4),Z),(np.array([1,-1,0,0.]),Z),(Z,np.array([0,0,1,-1.]))]
    Yb.append((np.array([-1,-1,1,1.]),Z) if cho=='A' else (Z,np.array([1,1,-1,-1.])))
    B=[]; M=np.zeros((4,5)); M[0,0]=1; M[1,0]=-1; B.append(M)
    ph=[f0,0,0,f3]; aa=[4,0,0,0]
    for k,(p,q) in enumerate(Yb):
        M=np.zeros((4,5)); M[0,0]=-ph[k]/2; M[1,0]=-ph[k]/2; M[2,0]=-aa[k]; M[3,0]=ph[k]; M[2,1:]=p; M[3,1:]=q; B.append(M)
    return np.array(B,dtype=complex)
rg=np.random.default_rng(3)
for cho,f0,f3 in [('A',2,2),('A',1.3,0.7)]:
    B=mk(cho,f0,f3); X=np.zeros((5,5,5),complex); X[:,1:,:]=B
    rows=[rk(B[:,i,:]) for i in range(4)]; cols=[rk(B[:,:,j]) for j in range(5)]
    T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:])
    n,r,bd=FO2(X,rg)
    try: t2=T2test(B,rg)
    except Exception as e: t2=str(e)
    print('cho %s f0 %s f3 %s: level/G err %.1e rows %s cols %s dim T_1 %d dim Omega %d | FO2 (dimT1, rank, bound) = (%d,%d,%d) | T2 %s'%(cho,f0,f3,check(B,rg),rows,cols,len(T),pr,n,r,bd,t2),flush=True)
    print(np.real(B).astype(int) if cho=='A' and f0==2 else '')
np.save('/home/kevxhk/work/L-gct-210/stage2/r9/cand_D04_MAi_f2.npy',mk('A',2,2))
