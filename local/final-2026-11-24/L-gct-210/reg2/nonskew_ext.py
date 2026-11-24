# Round 9, target 3 (evidence, calibrated): can a 5-dim level space S5 be extended to a 6-dim level space by a NON-SKEW two-column element
# E = x e_a^T + y e_b^T with sum x = 1?  For S5 = random hyperplanes of the saved 6-dim spaces (and the 5-dim census spaces), all column pairs,
# LM on (x, y) (8 unknowns) with residual = level polynomial at points of S5 + C E, plus sum x - 1.  Calibration: the same with sum x = 0 and
# |x| = 1 (re-finds the deleted direction when it is a two-column element, e.g. a skew-block or single-column element).
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
from t import level_err
from a5 import onb, rref_tol
mode=sys.argv[1]; rg=np.random.default_rng(int(sys.argv[2])); nfiles=int(sys.argv[3])
files=sorted(glob.glob(sys.argv[4])) if len(sys.argv)>4 else sorted(glob.glob('dr35_u*_s*.npy'))+sorted(glob.glob('ec_*.npy'))+['Mstar2.npy']
rg.shuffle(files); files=files[:nfiles]
def lm(S5,a,b,starts=3,rp=(1,2)):
    C=rg.normal(size=(140,6))+1j*rg.normal(size=(140,6)); sols=[]
    def build(z):
        E=np.zeros((4,5),complex); E[:,a]=z[:4]; E[:,b]=z[4:]; return np.concatenate([S5,E[None]],0)
    def res(z):
        r=F45(np.einsum('nk,kij->nij',C,build(z)))-120
        minor=z[rp[0]]*z[4+rp[1]]-z[rp[1]]*z[4+rp[0]]
        extra=([10*(z[:4].sum()-1)] if mode=='nonskew' else [10*z[:4].sum()])+[10*(minor-1)]
        return np.concatenate([r,extra])
    for s in range(starts):
        z=rg.normal(size=8)+1j*rg.normal(size=8); r=res(z); c=np.linalg.norm(r)
        for it in range(60):
            J=np.empty((len(r),8),complex)
            for k in range(8):
                zp=z.copy(); zp[k]+=1e-7; J[:,k]=(res(zp)-r)/1e-7
            dz=np.linalg.lstsq(J,-r,rcond=None)[0]; zn=z+dz; rn=res(zn)
            if np.linalg.norm(rn)<c: z,r,c=zn,rn,np.linalg.norm(rn)
            else: z=z+0.3*dz; r=res(z); c=np.linalg.norm(r)
            if c<1e-10: break
        if c<1e-8:
            M=onb(build(z))
            if len(M)==6 and level_err(M,ntest=15)<1e-8:
                from pieces import lines
                from t import rank as _rk
                L=lines(M); E=build(z)[-1].reshape(1,-1)
                inline=(len(L)>0 and _rk(np.concatenate([L,E],0),1e-6)==_rk(L,1e-6))
                if not inline:
                    # decomposability filter: does the two-column piece of M contain a LINE element with sum x != 0 (a single-row element
                    # e_i (alpha e_a + beta e_b) with alpha != 0)?  If so E = (that line) + (sum-zero part): not a genuine non-skew block.
                    from pieces import sub_supported
                    dec=False if mode=='nonskew' else None   # the filter is for NON-skew hits only (skew-mode hits are skew by construction)
                    for i in (range(4) if dec is not None else []):
                        mask=np.zeros((4,5),bool); mask[i,a]=True; mask[i,b]=True
                        Pl=sub_supported(M,mask)
                        if len(Pl) and np.abs(Pl[:,i,a]).max()>1e-6: dec=True
                    if not dec: sols.append(z)
                    else: print('   (decomposable hit filtered: single-row element with sum x != 0 present)',flush=True)
    return sols
tot=0; hits=0
for f in files:
    B=onb(np.load(f))
    for h in range(1):
        cvec=rg.normal(size=6)+1j*rg.normal(size=6); P=np.linalg.svd(cvec[None])[2][1:]     # 5 x 6: a random hyperplane
        S5=onb(np.einsum('kc,cab->kab',P,B))
        for a in range(5):
            for b in range(a+1,5):
                for rp in ((0,1),(0,2),(0,3),(1,2),(1,3),(2,3)):
                    tot+=1; s=lm(S5,a,b,starts=2,rp=rp)
                    if s: hits+=1; print('%s %s hyperplane %d cols (%d,%d) rows %s: %d solutions'%(mode,f,h,a,b,rp,len(s)),flush=True)
print('%s: %d (space, hyperplane, column pair) cases with a level extension, out of %d'%(mode,hits,tot))
