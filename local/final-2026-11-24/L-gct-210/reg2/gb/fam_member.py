# Round 14, target 2: does a numerically given 6-dim level space M lie in a deformed family F(params, t) up to row/column permutations?
# For every (sigma, tau) in S_4 x S_5 mapping M's line signature onto the family's, minimise the subspace residual |(I - P_F) Q_M| over the
# complex parameters (Levenberg-Marquardt on real/imaginary parts, several starts).  usage: fam_member.py MFILE FAMILY kind idx tgt [tol]
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from scipy.optimize import least_squares
mfile=sys.argv[1]; argv=sys.argv[2:6]; TOL=float(sys.argv[6]) if len(sys.argv)>6 else 1e-4
sys.argv=['x']+argv; exec(open('/home/kevxhk/work/L-gct-210/reg2/gb/fam_sig.py').read().split("if __name__=='__main__':")[0])
def lines_sig(M,tol):
    def nul(A):
        u,s,vh=np.linalg.svd(A); return int((s<tol*s[0]).sum())+max(0,A.shape[1]-len(s))
    a=[nul(M.reshape(len(M),-1)[:,~np.eye(4,dtype=bool)[i][:,None].repeat(5,1).ravel()].T) for i in range(4)]
    b=[nul(M.reshape(len(M),-1)[:,~np.eye(5,dtype=bool)[c][None,:].repeat(4,0).ravel()].T) for c in range(5)]
    return a,b
M=np.load(mfile); M=M/np.abs(M).max(); u,s,vh=np.linalg.svd(M.reshape(6,-1)); Q=vh[:6].conj().T        # 20 x 6 orthonormal (Hermitian)
aM,bM=lines_sig(vh[:6].reshape(6,4,5),TOL)
rg=np.random.default_rng(0); v0=[complex(rg.normal(),rg.normal()) for _ in P0]; F0=build(v0,0.6+0.3j)
uf,sf,vf=np.linalg.svd(F0.reshape(len(F0),-1)); F0=vf[:6].reshape(6,4,5); aF,bF=lines_sig(F0,1e-8)
perms=[(p,q) for p in itertools.permutations(range(4)) for q in itertools.permutations(range(5)) if [aM[p[i]] for i in range(4)]==aF and [bM[q[c]] for c in range(5)]==bF]
print('M signature',aM,bM,' family signature',aF,bF,' admissible permutations',len(perms),flush=True)
npar=len(P0)+1
def resid(x,Qp):
    z=x[:npar]+1j*x[npar:]; F=build(list(z[:-1]),z[-1]).reshape(len(Bs),-1)
    uf,sf,vf=np.linalg.svd(F); B=vf[:6].conj().T                     # 20 x 6 Hermitian ONB of span(F)
    R=Qp-B@(B.conj().T@Qp); return np.concatenate([R.real.ravel(),R.imag.ravel()])
best=(1e9,None)
for (p,q) in perms:
    Mp=vh[:6].reshape(6,4,5)[:,list(p),:][:,:,list(q)]                  # row i of Mp = row p[i] of M
    Qp=np.linalg.qr(Mp.reshape(6,-1).T)[0]
    for st in range(int(__import__("os").environ.get("NSTART","4"))):
        x0=rg.normal(size=2*npar)
        # round 14: two stages -- first the undeformed base (t = 0 fixed), then free t from the base optimum (rows-team spaces have tiny t)
        def resid0(y,Qp=Qp):
            x=np.zeros(2*npar); x[:npar-1]=y[:npar-1]; x[npar:2*npar-1]=y[npar-1:]; return resid(x,Qp)
        try:
            r0=least_squares(resid0,np.concatenate([x0[:npar-1],x0[npar:2*npar-1]]),method='lm',max_nfev=300)
            x1=np.zeros(2*npar); x1[:npar-1]=r0.x[:npar-1]; x1[npar:2*npar-1]=r0.x[npar-1:]; x1[npar-1]=1e-3
            r=least_squares(resid,x1,args=(Qp,),method='lm',max_nfev=400)
        except Exception as e: continue
        c=np.linalg.norm(r.fun)
        if c<best[0]: best=(c,(p,q,r.x[:npar]+1j*r.x[npar:]))
        if c<1e-6: break
    if best[0]<1e-6: break
c,info=best
np.set_printoptions(linewidth=400); print('%s in %s %s: best residual %.2e %s'%(mfile.split('/')[-1],argv[0],' '.join(argv[1:]),c,('perm '+str(info[0])+' '+str(info[1])+' params '+str(np.round(info[2],6)).replace(chr(10),' ')) if info else ''))
