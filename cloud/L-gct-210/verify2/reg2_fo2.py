# verify2 round 4: FO / FO2 / Omega for rows' 6-dim 4x5 level spaces (embedded with zero row r = 4), own code (fo2lib).
import numpy as np, sys, glob, itertools
sys.path.insert(0,'/home/claude/work/L-gct-210/verify2')
import fo2lib
J=np.ones((5,5))
def perm5(A): return sum(np.prod([A[i,p[i]] for i in range(5)]) for p in itertools.permutations(range(5)))
files=sorted(glob.glob('/home/claude/work/L-gct-210/rows/clm_p4_d6_defect3_*.npy')+glob.glob('/home/claude/work/L-gct-210/rows/nc_d6_k1_*.npy')+glob.glob('/home/claude/work/L-gct-210/rows/seed_d6_e3_*.npy'))+['/home/claude/work/L-gct-210/rows/rc45.npy']
sel=sys.argv[1:] or None
rng=np.random.default_rng(11)
for f in files:
    name=f.split('/')[-1][:-4]
    if sel and not any(s in name for s in sel): continue
    B4=np.asarray(np.load(f),dtype=complex)
    if B4.ndim!=3 or B4.shape[1:]!=(4,5): print(name,'shape',B4.shape,'skipped'); continue
    d=len(B4); B=np.zeros((d,5,5),complex); B[:,:4,:]=B4
    # level error at random points of norm ~1
    err=0
    for _ in range(6):
        c=rng.normal(size=d)+1j*rng.normal(size=d); c/=np.linalg.norm(c)
        err=max(err,abs(perm5(J+np.tensordot(c,B,axes=1))-120))
    out=[]
    for tol in (1e-9,1e-6):
        def fo2(npts=60,nq=5):
            def pt():
                c=rng.normal(size=d)+1j*rng.normal(size=d); return J+np.tensordot(c,B,axes=1)
            A=np.array([fo2lib.cof(pt()) for _ in range(npts)])
            u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol*s[0])); N=vh[r:].conj().T
            Q=sum((rng.normal()+1j*rng.normal())*fo2lib.hess(pt()) for _ in range(nq))
            G=N.T@Q@N; sg=np.linalg.svd(G,compute_uv=False); rq=int(np.sum(sg>tol*1e2*max(1,sg[0])))
            Om=N.reshape(5,5,-1)[4]          # row-4 projection of T_1 (5 x dimT)
            so=np.linalg.svd(Om,compute_uv=False); ro=int(np.sum(so>tol*1e2*max(1,so[0])))
            return N.shape[1],rq,N.shape[1]-(rq+1)//2,ro,s[r-1]/s[0],(s[r]/s[0] if r<len(s) else 0),sg,so
        out.append(fo2())
    a,b=out
    print('%-24s dim %d level err %.0e | tol 1e-9: T_1 %2d rank %d bound %d Omega %d (sv gap %.0e|%.0e) | tol 1e-6: T_1 %2d rank %d bound %d Omega %d'%(
        name,d,err,a[0],a[1],a[2],a[3],a[4],a[5],b[0],b[1],b[2],b[3]),flush=True)
    if '-v' in sys.argv: print('    q singular values (tol 1e-6 run):',np.array2string(b[6][:8],precision=2),' Omega sv:',np.array2string(b[7],precision=2))
