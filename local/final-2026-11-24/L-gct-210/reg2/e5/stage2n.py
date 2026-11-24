# Round 17: NUMERICAL GENERIC LINEAR TEST for stage 2 (a MEASURE, not a proof).  For a type and each incidence class whose stage-1 line
# components are cached: take a random point of each component (Gauss-Newton on the component + dim(C) random linear slices), evaluate the
# equations of degree <= 1 in the genuine element G (P_2-mixed and all degree-1 terms, + sums for R1/C1) there, and report the kernel
# dimension of this linear system in G (0 => at GENERIC points of the component G = 0 is forced; solutions can only live on the rank-drop locus).
# usage: stage2n.py A B KIND P Q GTYPE
import sys, os, json, hashlib, itertools, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import numpy as np, sympy as sp
from famtool import *
src=open('/home/kevxhk/work/L-gct-210/reg2/e5/twostage.py').read()
pre=src.split('res={}')[0]
exec(pre)          # defines A, Bd, kind, P, Q, gt, rows, cols, classes, lines_of, elems, stage1 (cached), sing ...
rng=np.random.default_rng(7)
out={}
for bits in classes:
    s1=stage1(bits)
    if s1['verdict']!='LINES': out.setdefault(s1['verdict'],[]).append(''.join(map(str,bits))); continue
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    rowel,colel,params=lines_of(S); L=5 if kind=='row' else 4
    gx=['gx%d'%k for k in range(L)]; gy=['gy%d'%k for k in range(L)]; pall=params+gx+gy
    F=Family(pall,lambda R,V: elems(R,V,rowel,colel,(gx,gy)),len(rowel)+len(colel)+1); np_=len(pall)
    lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    gidx=[pall.index(v) for v in gx+gy]; lidx=[pall.index(v) for v in params]
    kerdims=[]
    for comp in s1['comps']:
        syms=sp.symbols(' '.join(params)); syms=list(syms) if isinstance(syms,(list,tuple)) else [syms]
        gens=[sp.sympify(g.replace('^','**')) for g in comp.split(',') if g.strip()]
        # dimension of the component
        dd=sing('ring R=0,(%s),dp;\nideal I=%s;\nprint(dim(std(I)));\nquit;\n'%(','.join(params),comp),60)
        try: dimC=int(dd.strip().split()[-1])
        except Exception: kerdims.append('dim?'); continue
        f=sp.lambdify(syms,gens,'numpy'); Jf=sp.lambdify(syms,sp.Matrix(gens).jacobian(syms),'numpy')
        best=None
        for trial in range(6):
            Ls=rng.normal(size=(dimC,len(syms)))+1j*rng.normal(size=(dimC,len(syms))); bs=rng.normal(size=dimC)+1j*rng.normal(size=dimC)
            z=rng.normal(size=len(syms))+1j*rng.normal(size=len(syms))
            for it in range(100):
                r=np.concatenate([np.array(f(*z),complex).ravel(),Ls@z-bs]); J=np.concatenate([np.array(Jf(*z),complex).reshape(len(gens),len(syms)),Ls])
                dz=np.linalg.lstsq(J,-r,rcond=None)[0]; z=z+dz
                if np.linalg.norm(dz)<1e-13*(1+np.linalg.norm(z)): break
            res=np.linalg.norm(np.array(f(*z),complex))
            if res<1e-9 and (best is None or res<best[0]): best=(res,z)
            if best and best[0]<1e-11: break
        if best is None: kerdims.append('nopoint'); continue
        z=best[1]; val={pall[i]:z[k] for k,i in enumerate(lidx)}
        rowsL=[]
        for q in lev:
            row=np.zeros(len(gidx),complex); deg1=False
            for k,v in q.items():
                dg=sum(k[i] for i in gidx)
                if dg==1:
                    gi=[a for a,i in enumerate(gidx) if k[i]][0]; m=complex(v)
                    for a,i in enumerate(lidx): m*=val[pall[i]]**k[i] if k[i] else 1
                    row[gi]+=m; deg1=True
            if deg1: rowsL.append(row)
        if gt in ('R1','C1'):
            e1=np.zeros(len(gidx)); e1[:L]=1; e2=np.zeros(len(gidx)); e2[L:]=1; rowsL+= [e1,e2]
        Lm=np.array(rowsL); sv=np.linalg.svd(Lm,compute_uv=False); rk=int((sv>1e-8*max(1,sv[0])).sum())
        if os.environ.get('QUAD'):
            # round 18: quadratic stage at the same generic point: genuine kernel (complement of the gauge) -> solve the degree-2 equations
            u_,sv_,vh_=np.linalg.svd(Lm); Kb=vh_[rk:].conj()                      # kernel basis (rows), in g coordinates
            gauge=[]
            for (r_,v_) in rowel if kind=='row' else colel:
                if r_ in (P,Q):
                    vec=np.array([val[x] if x else 0 for x in v_],complex); gv=np.zeros(len(gidx),complex)
                    if r_==P: gv[:L]=vec
                    else: gv[L:]=vec
                    gauge.append(gv)
            Gm=np.array(gauge) if gauge else np.zeros((0,len(gidx)))
            # complement of span(gauge) inside the kernel
            if len(Gm):
                Qg,_=np.linalg.qr(Gm.T); Kc=Kb-(Kb@Qg.conj())@Qg.T
                uu,ss,vv=np.linalg.svd(Kc); Kc=vv[:int((ss>1e-8*max(1,ss[0])).sum())].conj() if len(ss) else np.zeros((0,len(gidx)))
                # vv rows span the row space of Kc
            else: Kc=Kb
            kgen=len(Kc)
            if kgen==0: kerdims.append(('quad','genkernel0')); continue
            quads=[]
            for q in lev:
                terms=[]
                for k,v in q.items():
                    if sum(k[i] for i in gidx)==2:
                        m=complex(v)
                        for a,i in enumerate(lidx):
                            if k[i]: m*=val[pall[i]]**k[i]
                        gi=[a for a,i in enumerate(gidx) for _ in range(k[i])]
                        terms.append((m,gi[0],gi[1]))
                if terms: quads.append(terms)
            def qres(c):
                g=c@Kc; return np.array([sum(m*g[a]*g[b] for (m,a,b) in t) for t in quads],complex)
            lin=rng.normal(size=kgen)+1j*rng.normal(size=kgen); found=None
            if gt=='N':
                # normalise s = sum(x) = 1 (an N element needs s != 0); if s vanishes on the whole genuine kernel, N is impossible here
                ones=np.zeros(len(gidx)); ones[:L]=1; lin=Kc@ones
                if np.linalg.norm(lin)<1e-8: kerdims.append(('quad','s=0-forced',kgen)); continue
            for trial in range(12):
                c=rng.normal(size=kgen)+1j*rng.normal(size=kgen); c=c/(lin@c)
                for it in range(60):
                    r_=np.concatenate([qres(c),[lin@c-1]]); J=np.empty((len(r_),kgen),complex); h=1e-7
                    for a in range(kgen):
                        cp=c.copy(); cp[a]+=h; J[:,a]=(np.concatenate([qres(cp),[lin@cp-1]])-r_)/h
                    dc=np.linalg.lstsq(J,-r_,rcond=None)[0]; c=c+dc
                    if np.linalg.norm(dc)<1e-12: break
                rr=np.linalg.norm(qres(c))/max(1,np.linalg.norm(c))**2
                if rr<1e-8: found=c; break
            if found is None: kerdims.append(('quad','nosol',kgen))
            else:
                g=found@Kc
                zz=np.linalg.norm(g[:L]+g[L:])/np.linalg.norm(g) if kind=='row' else -1
                # support of the solution (which coordinates of x, y are nonzero)
                supp=''.join('1' if abs(t)>1e-6*np.linalg.norm(g) else '0' for t in g)
                kerdims.append(('quad','sol',kgen,round(float(zz),4),supp))
            continue
        if os.environ.get('ZTEST') and kind=='row':
            # round 18: add z = x + y = 0 (G = (e_r - e_j) (x) x); compare kernel dimensions
            Z=np.zeros((L,len(gidx))); Z[:,:L]=np.eye(L); Z[:,L:]=np.eye(L)
            sv2=np.linalg.svd(np.concatenate([Lm,Z]),compute_uv=False); rk2=int((sv2>1e-8*max(1,sv2[0])).sum())
            kerdims.append((len(gidx)-rk,len(gidx)-rk2))
        else: kerdims.append(len(gidx)-rk)
    key='kernel dims %s'%kerdims
    out.setdefault('LINEAR-GENERIC-KILL' if all(k==0 for k in kerdims) else key,[]).append(''.join(map(str,bits)))
print(tag+': %d classes -> '%len(classes)+'; '.join('%s x%d'%(k,len(v)) for k,v in sorted(out.items())),flush=True)
