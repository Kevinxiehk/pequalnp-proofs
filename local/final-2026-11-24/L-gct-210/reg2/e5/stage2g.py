# Round 18: GLOBAL numerical solve of the full e = 5 system (a MEASURE for the special loci, not a proof).  Unknowns: the line parameters p AND
# the genuine element G together; equations: the stage-1 component, ALL level equations of M = Lin (+) <G> (G-degree 1 and 2), sums (R1/C1),
# a chart (N: sum x = 1; R1/C1: random linear form = 1), and a random BILINEAR gauge fixing B(x, u) = 0 for every row line u on line P (resp. Q
# with y).  Gauss-Newton (min-norm lstsq steps, analytic Jacobian) from NST random starts.  Each converged solution: M = 5 lines + G is checked
# for level error, rank 6, and its single-row/column part dimensions (sum > 5 => e >= 6, closed by the e = 6 classification).  Prints per
# class the counts ('gen5' = a genuine e = 5 member candidate; dumped to reg2/e5/dumpg/).   usage: stage2g.py A B KIND P Q GTYPE [NST]
import sys, os; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, sympy as sp
from famtool import *
from t import rowpart, colpart, level_err
from a5 import onb
NST=int(sys.argv[7]) if len(sys.argv)>7 else 12
RANK1=bool(os.environ.get('RANK1'))   # ansatz y = -x (G = (e_P - e_Q) (x) x), the shape of every known e <= 5 genuine element
src=open('/home/kevxhk/work/L-gct-210/reg2/e5/twostage.py').read(); pre=src.split('res={}')[0]
sys.argv=sys.argv[:7]+['60']; exec(pre)
rng=np.random.default_rng(11); out={}
def polyarr(polys,nv):
    E=[];C=[];I=[]
    for qi,q in enumerate(polys):
        for k,v in q.items(): E.append(list(k)+[0]*(nv-len(k))); C.append(complex(v)); I.append(qi)
    return np.array(E,int),np.array(C,complex),np.array(I,int)
for bits in classes:
    s1=stage1(bits)
    if s1['verdict']!='LINES': continue
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    rowel,colel,params=lines_of(S); L=5 if kind=='row' else 4
    gx=['gx%d'%k for k in range(L)]; gy=['gy%d'%k for k in range(L)]; pall=params+gx+gy; nv=len(pall)
    F=Family(pall,lambda R,V: elems(R,V,rowel,colel,(gx,gy)),len(rowel)+len(colel)+1)
    lev=[{k[:nv]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    gidx=[pall.index(v) for v in gx+gy]
    E,Cf,Iq=polyarr(lev,nv); nq=len(lev)
    same=rowel if kind=='row' else colel
    res_cls=[]
    for comp in s1['comps']:
        syms=list(sp.symbols(' '.join(pall)))
        gens=[sp.sympify(g.replace('^','**')) for g in comp.split(',') if g.strip()]
        fC=sp.lambdify(syms,gens,'numpy'); jC=sp.lambdify(syms,sp.Matrix(gens).jacobian(syms),'numpy')
        beta=rng.normal(size=L)+1j*rng.normal(size=L)
        gf=[]
        for (r_,v_) in same:
            if r_ in (P,Q): gf.append((r_,[pall.index(x) if x else None for x in v_]))
        charts=[]                               # one random linear chart per line vector (the system is multihomogeneous in each line)
        for (r_,v_) in rowel+colel:
            a=np.zeros(nv,complex)
            for x in v_:
                if x: a[pall.index(x)]=rng.normal()+1j*rng.normal()
            charts.append(a)
        charts=np.array(charts)
        lin=np.zeros(nv,complex)
        if gt=='N': lin[[pall.index(x) for x in gx]]=1
        else: lin[gidx]=rng.normal(size=2*L)+1j*rng.normal(size=2*L)
        gP=[ix for (r_,ix) in gf if r_==P]; gQ=[ix for (r_,ix) in gf if r_==Q]
        def gramdet(z,ixs):
            if not ixs: return None
            U=np.array([[z[i] if i is not None else 0 for i in ix] for ix in ixs]); return np.linalg.det((U*beta[None,:])@U.T)
        bL=rng.normal(size=20)+1j*rng.normal(size=20)
        def linemat(z):
            Ms=[]
            for (r_,v_) in rowel:
                m_=np.zeros((4,5),complex); m_[r_]=[z[pall.index(x)] if x else 0 for x in v_]; Ms.append(m_.ravel())
            for (c_,v_) in colel:
                m_=np.zeros((4,5),complex); m_[:,c_]=[z[pall.index(x)] if x else 0 for x in v_]; Ms.append(m_.ravel())
            return np.array(Ms)
        def F_(zz):
            z=zz[:nv]; wP,wQ,wL=zz[nv],zz[nv+1],zz[nv+2]
            Lm_=linemat(z); rab=[np.linalg.det((Lm_*bL[None,:])@Lm_.T)*wL-1]
            if gP: rab.append(gramdet(z,gP)*wP-1)
            if gQ: rab.append(gramdet(z,gQ)*wQ-1)
            return np.concatenate([F0(z),np.array(rab,complex)])
        def J_(zz):
            z=zz[:nv]; J0=J0_(z); n0=J0.shape[0]; rows_=[]
            r0=F_(zz)[n0:]; Jr=np.zeros((len(r0),nv+3),complex); h=1e-7
            for v in range(nv+3):
                zp=zz.copy(); zp[v]+=h; Jr[:,v]=(F_(zp)[n0:]-r0)/h
            return np.concatenate([np.concatenate([J0,np.zeros((n0,3))],axis=1),Jr])
        def F0(z):
            mon=Cf*np.prod(z[None,:]**E,axis=1); r=np.zeros(nq,complex); np.add.at(r,Iq,mon)
            ex=list(charts@z-1)+[lin@z-1]
            if RANK1: ex+=[z[pall.index(gx[c])]+z[pall.index(gy[c])] for c in range(L)]
            if gt in ('R1','C1'): ex+=[sum(z[pall.index(x)] for x in gx), sum(z[pall.index(x)] for x in gy)]
            for (r_,ix) in gf:
                gg=gx if r_==P else gy
                ex.append(sum(beta[c]*z[pall.index(gg[c])]*z[ix[c]] for c in range(L) if ix[c] is not None))
            return np.concatenate([np.array(fC(*z),complex).ravel(),r,np.array(ex,complex)])
        def J0_(z):
            Jl=np.zeros((nq,nv),complex)
            for v in range(nv):
                m=E[:,v]>0
                if not m.any(): continue
                Ev=E[m].copy(); c=Cf[m]*Ev[:,v]; Ev[:,v]-=1
                mon=c*np.prod(z[None,:]**Ev,axis=1); np.add.at(Jl[:,v],Iq[m],mon)
            ex=list(charts)+[lin.copy()]
            if RANK1:
                for c in range(L):
                    a=np.zeros(nv,complex); a[pall.index(gx[c])]=1; a[pall.index(gy[c])]=1; ex.append(a)
            if gt in ('R1','C1'):
                a=np.zeros(nv,complex); a[[pall.index(x) for x in gx]]=1; ex.append(a)
                a=np.zeros(nv,complex); a[[pall.index(x) for x in gy]]=1; ex.append(a)
            for (r_,ix) in gf:
                gg=gx if r_==P else gy; a=np.zeros(nv,complex)
                for c in range(L):
                    if ix[c] is not None: a[pall.index(gg[c])]+=beta[c]*z[ix[c]]; a[ix[c]]+=beta[c]*z[pall.index(gg[c])]
                ex.append(a)
            return np.concatenate([np.array(jC(*z),complex).reshape(len(gens),nv),Jl,np.array(ex)])
        cnt={'gen5':0,'e6':0,'inLin':0,'fail':0,'nonlevel':0}
        for st in range(NST):
            z=rng.normal(size=nv+3)+1j*rng.normal(size=nv+3)
            ok=False
            for it in range(120):
                r=F_(z); J=J_(z); dz=np.linalg.lstsq(J,-r,rcond=None)[0]; z=z+dz
                if np.linalg.norm(dz)<1e-12*(1+np.linalg.norm(z)): ok=True; break
                if np.linalg.norm(z)>1e8: break
            if np.linalg.norm(F_(z))>1e-9*(1+np.linalg.norm(z))**4: cnt['fail']+=1; continue
            val=dict(zip(pall,z[:nv])); Bm=[]
            for (r_,v_) in rowel:
                m_=np.zeros((4,5),complex); m_[r_]=[val[x] if x else 0 for x in v_]; Bm.append(m_)
            for (c_,v_) in colel:
                m_=np.zeros((4,5),complex); m_[:,c_]=[val[x] if x else 0 for x in v_]; Bm.append(m_)
            m_=np.zeros((4,5),complex)
            if kind=='row': m_[P]=[val[x] for x in gx]; m_[Q]=[val[x] for x in gy]
            else: m_[:,P]=[val[x] for x in gx]; m_[:,Q]=[val[x] for x in gy]
            Bm.append(m_); Bm=np.array(Bm)
            sv=np.linalg.svd(Bm.reshape(len(Bm),20),compute_uv=False)
            if sv[-1]<1e-7*sv[0]:
                cnt['inLin']+=1
                if os.environ.get('DBG'):
                    sl=np.linalg.svd(Bm[:5].reshape(5,20),compute_uv=False); print('DBG inLin: sv6',np.round(sv,8),' lines sv',np.round(sl,8),' |z|=%.1e'%np.linalg.norm(z),' |G|=%.2e'%np.linalg.norm(Bm[5]),flush=True)
                continue
            Bo=onb(Bm)
            if level_err(Bo,ntest=10)>1e-7: cnt['nonlevel']+=1; continue
            e_=sum(len(rowpart(Bo,[i])) for i in range(4))+sum(len(colpart(Bo,[j])) for j in range(5))
            if e_>5: cnt['e6']+=1; continue
            cnt['gen5']+=1
            os.makedirs('/home/kevxhk/work/L-gct-210/reg2/e5/dumpg',exist_ok=True)
            np.save('/home/kevxhk/work/L-gct-210/reg2/e5/dumpg/%s_%s_%s_%d_%d_%s_%s_%d.npy'%(sys.argv[1],sys.argv[2],kind,P,Q,gt,''.join(map(str,bits)),st),Bm)
        res_cls.append(tuple(sorted((k,v) for k,v in cnt.items() if v)))
    print('GCLASS',tag,''.join(map(str,bits)),res_cls,flush=True)
    key='GEN5' if any(dict(c).get('gen5',0) for c in res_cls) else 'no-gen5'
    out.setdefault(key,[]).append(''.join(map(str,bits)))
print(tag+': -> '+'; '.join('%s x%d'%(k,len(v)) for k,v in sorted(out.items())),flush=True)
