import sys, numpy as np, itertools
sys.argv=[sys.argv[0],'1','0','full']
src=open('/home/claude/work/L-gct-210/stage2/r4_N2inj.py').read().split("if __name__=='__main__':")[0]
exec(src)
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); from pairlib import rank, nullspace
np.set_printoptions(precision=4,suppress=True,linewidth=220)
z=np.load('/tmp/r4_N2inj_full_1.npy'); par=maps(z); Pc,Pd,Pe,ra,rb,oa,ob=par
rg2=np.random.default_rng(99); pts=rg2.normal(size=(40,6))+1j*rg2.normal(size=(40,6)); m=build(par,pts)
print('level defect on fresh points: %.2e'%abs(perm5(1+m)-120).max())
for row in (0,1):
    p=pts.copy(); p[:,row]=0; x=np.delete(build(par,p),row,axis=1)
    print(' G defect on L_%s: %.2e'%('ab'[row],max(abs(perm4(np.delete(x,j,axis=2))).max() for j in range(5))))
# basis of M: 6 parameter unit vectors
B=build(par,np.eye(6,dtype=complex)); print('dim M =',rank(B.reshape(6,-1)))
print('Psi_c=\n',Pc,'\nPsi_d=\n',Pd,'\nPsi_e=\n',Pe); print('rho_a=',ra,'\nrho_b=',rb,'\nom_a=',oa,' om_b=',ob)
for i,nm in enumerate('abcde'): print(' row',nm,'projection dim',rank(B[:,i,:]))
for j in range(5):
    ns=nullspace(B[:,:,j]); print(' column',j,'projection dim',rank(B[:,:,j]),' annihilator(s):',np.round(ns.T,3).tolist() if ns.shape[1]<=2 else ns.shape)
