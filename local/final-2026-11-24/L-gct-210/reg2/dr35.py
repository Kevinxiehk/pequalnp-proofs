# Round 6, structure route: 6-dim 4x5 level spaces with a deletable row (strong sense): M = e_0 (x) U (+) S, U = u-dim subspace of 1^perp in C^5
# (row 0), S = (6-u)-dim space of 3x5 matrices in rows 1..3 with zero entry sum.  Then S is a 3x5 level space with dim S - e(S) >= 2 (= 2 iff U
# is saturated).  Holomorphic Gauss-Newton in random Grassmannian charts (no normalisation penalty).  For each solution: e(S), polishing,
# sparse limit (rref + rounding), single-row / single-column parts of S, line-spannedness, (dim Omega, dim T_1, FO2) of M.
# usage: dr35.py SEED u NSTARTS [save]
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from ext6 import F45
from t import rank, null, level_err
rg=np.random.default_rng(int(sys.argv[1])); u=int(sys.argv[2]); ns=int(sys.argv[3]); save='save' in sys.argv
d=6-u
H5=null(np.ones((1,5)))                       # 4 x 5, rows span 1^perp in C^5
H15=null(np.ones((1,15)))                     # 14 x 15, sum-zero 3x5 matrices
def build(z,QU,QS):
    zu=z[:u*(4-u)].reshape(u,4-u); zs=z[u*(4-u):].reshape(d,14-d)
    Uc=np.concatenate([np.eye(u),zu],1)@QU     # u x 4 coordinates in H5
    Sc=np.concatenate([np.eye(d),zs],1)@QS     # d x 14 coordinates in H15
    Uv=Uc@H5; Sv=(Sc@H15).reshape(d,3,5)
    B=np.zeros((6,4,5),complex)
    for a in range(u): B[a,0]=Uv[a]
    for a in range(d): B[u+a,1:]=Sv[a]
    return B
def solve(iters=80):
    nz=u*(4-u)+d*(14-d); N=3*nz+30
    QU=np.linalg.qr(rg.normal(size=(4,4))+1j*rg.normal(size=(4,4)))[0]; QS=np.linalg.qr(rg.normal(size=(14,14))+1j*rg.normal(size=(14,14)))[0]
    C=rg.normal(size=(N,6))+1j*rg.normal(size=(N,6))
    def res(z): return F45(np.einsum('nk,kij->nij',C,build(z,QU,QS)))-120
    z=(rg.normal(size=nz)+1j*rg.normal(size=nz))*0.4; r=res(z); c=np.linalg.norm(r); lam=1e-3
    for it in range(iters):
        h=1e-7; J=np.empty((len(r),nz),complex)
        for a in range(nz):
            zp=z.copy(); zp[a]+=h; J[:,a]=(res(zp)-r)/h
        A=J.conj().T@J; g=J.conj().T@r; ok=False
        for _ in range(6):
            dz=np.linalg.solve(A+lam*np.eye(nz)*max(1,np.abs(np.diag(A)).max()*1e-6),-g); zn=z+dz; rn=res(zn); cn=np.linalg.norm(rn)
            if cn<c: z,r,c=zn,rn,cn; lam=max(lam/4,1e-12); ok=True; break
            lam*=8
        if not ok or c<1e-11: break
    return c,build(z,QU,QS)
def sub_supported(S,mask):
    A=S.reshape(len(S),-1)[:,~mask.ravel()].T
    if A.shape[0]==0: return S
    Cn=null(A,1e-7); return np.einsum('kc,cab->kab',Cn,S) if len(Cn) else np.zeros((0,)+S.shape[1:])
def line_parts(S):            # S: (d,3,5)
    rows=[];cols=[]
    for i in range(3):
        m=np.zeros((3,5),bool); m[i]=True; rows.append(sub_supported(S,m))
    for j in range(5):
        m=np.zeros((3,5),bool); m[:,j]=True; cols.append(sub_supported(S,m))
    P=[p.reshape(len(p),-1) for p in rows+cols if len(p)]
    r=rank(np.concatenate(P,0),1e-6) if P else 0
    return r,[len(p) for p in rows],[len(p) for p in cols]
def defect_e(B,n=40):
    V=[]
    for _ in range(n):
        c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); Y=np.einsum('k,kab->ab',c,B); A=np.ones((4,5))+Y
        V.append([np.sum(np.prod(np.delete(A,j,axis=1)[np.arange(4)[:,None],np.array(list(itertools.permutations(range(4)))).T],axis=0))-24 for j in range(5)])
    return rank(np.array(V),1e-6)
if __name__=='__main__':
    from a5 import onb
    hits=0
    for s in range(ns):
        c,B=solve()
        if c>1e-9: continue
        Bo=onb(B)
        if len(Bo)<6 or level_err(Bo,ntest=20)>1e-8: continue
        hits+=1; S=onb(B[u:,1:,:]); e=defect_e(np.concatenate([np.zeros((d,1,5)),S],1))
        r,rp,cp=line_parts(S)
        from a5 import rref_tol
        R=rref_tol(onb(Bo),1e-5); Ro=onb(R); lim=level_err(Ro,ntest=20)<1e-9
        if lim:
            S2=onb(Ro[:,1:,:][np.abs(Ro[:,1:,:]).reshape(len(Ro),-1).max(1)>1e-9]) if True else None
            S2=onb(np.array([m[1:] for m in Ro if np.abs(m[0]).max()<1e-9])) if any(np.abs(m[0]).max()<1e-9 for m in Ro) else np.zeros((0,3,5))
            r2,rp2,cp2=line_parts(S2) if len(S2) else (0,[],[])
        else: r2,rp2,cp2=-1,[],[]
        from nc_num import report as rep
        import io, contextlib
        buf=io.StringIO()
        with contextlib.redirect_stdout(buf): rep('x',Ro if lim else Bo)
        inv=buf.getvalue().split('dimOmega=')[1].split(' Omega=')[0] if 'dimOmega=' in buf.getvalue() else buf.getvalue()[:60]
        print('u=%d start %d: dim S %d e(S) %d | raw line-span %d/%d | sparse limit ok=%s line-span %d/%d rows %s cols %s | Omega,T1,FO2: %s'%(u,s,len(S),e,r,len(S),lim,r2,len(S2) if lim else -1,rp2,cp2,inv),flush=True)
        if save: np.save('/home/kevxhk/work/L-gct-210/reg2/dr35_u%d_s%s_%d.npy'%(u,sys.argv[1],s),Bo)
    print('u=%d: %d hits in %d starts'%(u,hits,ns))
