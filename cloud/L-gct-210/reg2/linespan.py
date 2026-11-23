# Census of LINE-SPANNED 6-dim 4x5 level spaces: M = sum of single-row parts e_i (x) U_i (dim u_i) and single-column parts V_c (x) e_c
# (dim v_c), sum u_i + sum v_c = 6.  Not seeded from known spaces; unknowns = entries of the basis vectors.  usage: SEED TMAX
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, itertools, time
from ext6 import F45, classify
from t import level_err
def parts(n,maxpart,maxlen):
    def rec(n,mx,ln):
        if n==0: yield (); return
        if ln==0: return
        for a in range(min(n,mx),0,-1):
            for r in rec(n-a,a,ln-1): yield (a,)+r
    return list(rec(n,maxpart,maxlen))
def build(z,u,v):
    B=[]; k=0
    for i,ui in enumerate(u):
        for _ in range(ui):
            m=np.zeros((4,5),complex); m[i,:]=z[k:k+5]; k+=5; B.append(m)
    for c,vc in enumerate(v):
        for _ in range(vc):
            m=np.zeros((4,5),complex); m[:,c]=z[k:k+4]; k+=4; B.append(m)
    return np.array(B)
def solve(u,v,rg,iters=120,N=260):
    nz=5*sum(u)+4*sum(v); C=rg.normal(size=(N,6))+1j*rg.normal(size=(N,6))
    def res(z):
        B=build(z,u,v); G=B.reshape(6,20); 
        # keep basis vectors normalised and (softly) orthonormal to avoid collapse
        Gm=G@G.conj().T-np.eye(6)
        return np.concatenate([F45(np.einsum('nk,kij->nij',C,B))-120, 3*Gm.ravel().real, 3*Gm.ravel().imag])
    z=(rg.normal(size=nz)+1j*rg.normal(size=nz))/2; r=res(z); c=np.linalg.norm(r); mu=1e-2
    for it in range(iters):
        h=1e-6; J=np.empty((len(r),2*nz))
        # residual is not holomorphic because of the normalisation terms: use real variables
        for a in range(nz):
            zp=z.copy(); zp[a]+=h; d1=(res(zp)-r)/h; zp=z.copy(); zp[a]+=1j*h; d2=(res(zp)-r)/h
            J[:,a]=0; 
            if a==0: Jc=np.empty((len(r),2*nz),complex)
            Jc[:,a]=d1; Jc[:,nz+a]=d2
        Jr=np.concatenate([Jc.real,Jc.imag],0); rr=np.concatenate([r.real,r.imag])
        A=Jr.T@Jr; g=Jr.T@rr
        for _ in range(8):
            dx=np.linalg.solve(A+mu*np.eye(2*nz),-g); zn=z+dx[:nz]+1j*dx[nz:]; rn=res(zn); cn=np.linalg.norm(rn)
            if cn<c: z=zn; r=rn; c=cn; mu=max(mu/5,1e-12); break
            mu*=6
        else: break
        if c<1e-11: break
    return c,build(z,u,v)
if __name__=='__main__':
    seed=int(sys.argv[1]); tmax=float(sys.argv[2]); rg=np.random.default_rng(seed); t0=time.time()
    pats=[]
    for k in range(0,7):
        for u in parts(k,3,4):
            for v in parts(6-k,3,5):
                pats.append((u+(0,)*(4-len(u)),v+(0,)*(5-len(v))))
    rg.shuffle(pats); tot={}; done=0
    for u,v in pats:
        if time.time()-t0>tmax: break
        done+=1; out=[]
        for trial in range(2):
            # random placement of the parts on rows / columns does not matter (symmetry); keep as is
            c,B=solve(u,v,rg)
            if c<1e-9 and np.linalg.matrix_rank(B.reshape(6,20),tol=1e-6)==6 and level_err(B)<1e-8:
                typ,desc=classify(B,rg); out.append((typ,desc)); tot[typ]=tot.get(typ,0)+1
                if typ=='OTHER': np.save('linespan_other_s%d_%d_%d.npy'%(seed,done,trial),B)
        print('u=%s v=%s: %s'%(u,v,[o[0] for o in out] if out else 'none'),flush=True)
        for typ,desc in out:
            if typ=='OTHER': print('     OTHER',desc)
    print('patterns done %d of %d; totals %s'%(done,len(pats),tot))
