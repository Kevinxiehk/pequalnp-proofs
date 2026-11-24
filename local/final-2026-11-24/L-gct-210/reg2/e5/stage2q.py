# Round 18 copy of stage2n.py with the QUADRATIC stage (classification gen/one/line).  Round 17: NUMERICAL GENERIC LINEAR TEST for stage 2 (a MEASURE, not a proof).  For a type and each incidence class whose stage-1 line
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
        if True:
            # QUADRATIC STAGE (round 18, numerical measure): genuine kernel K (mod gauge) at a generic component point; solve the degree-2
            # equations on K from 16 random starts; classify each solution: 'one' = single row/column matrix mod gauge (=> e would be 6, not
            # this type), 'line' = x or y in the gauge span (single line mod gauge), 'gen' = genuine.  For N the chart is s = sum(x) = 1.
            u_,sv_,vh_=np.linalg.svd(Lm); Kb=vh_[rk:].conj()
            gauge=[]
            same=rowel if kind=='row' else colel; other=colel if kind=='row' else rowel
            for (r_,v_) in same:
                if r_ in (P,Q):
                    vec=np.array([val[x] if x else 0 for x in v_],complex); gv=np.zeros(len(gidx),complex)
                    if r_==P: gv[:L]=vec
                    else: gv[L:]=vec
                    gauge.append(gv)
            bycol={}
            for (c_,v_) in other: bycol.setdefault(c_,[]).append(np.array([val[x] if x else 0 for x in v_],complex))
            for c_,vs in bycol.items():               # combinations of cross lines (same cross line index) supported on P, Q only
                Vm=np.array(vs); oth=[k for k in range(Vm.shape[1]) if k not in (P,Q)]
                uu_,ss_,vh2=np.linalg.svd(Vm[:,oth].T); rr_=int((ss_>1e-9*max(1,ss_[0] if len(ss_) else 1)).sum())
                for co in vh2[rr_:].conj():
                    vec=co@Vm; gv=np.zeros(len(gidx),complex); gv[c_]=vec[P]; gv[L+c_]=vec[Q]
                    if np.linalg.norm(gv)>1e-9: gauge.append(gv)
            Gm=np.array(gauge) if gauge else np.zeros((0,len(gidx)))
            if len(Gm):
                Qg,_=np.linalg.qr(Gm.T); Kc=Kb-(Kb@Qg.conj())@Qg.T
                uu,ss,vv=np.linalg.svd(Kc); Kc=vv[:int((ss>1e-8*max(1,ss[0])).sum())] if len(ss) else np.zeros((0,len(gidx)))
            else: Kc=Kb
            kgen=len(Kc)
            if kgen==0: kerdims.append(('Q0',)); continue
            quads=[]
            for q in lev:
                terms=[]
                for k,v in q.items():
                    if sum(k[i] for i in gidx)==2:
                        m=complex(v)
                        for a_,i in enumerate(lidx):
                            if k[i]: m*=val[pall[i]]**k[i]
                        gi=[a_ for a_,i in enumerate(gidx) for _ in range(k[i])]
                        terms.append((m,gi[0],gi[1]))
                if terms: quads.append(terms)
            def qres(c):
                g=c@Kc; return np.array([sum(m*g[a_]*g[b_] for (m,a_,b_) in t) for t in quads],complex)
            lin=rng.normal(size=kgen)+1j*rng.normal(size=kgen)
            if gt=='N':
                ones=np.zeros(len(gidx)); ones[:L]=1; lin=Kc@ones
                if np.linalg.norm(lin)<1e-8: kerdims.append(('Qs0',kgen)); continue
            def resid_in(g,idx):
                if not len(Gm): return np.linalg.norm(g[idx])
                A_=Gm[:,idx].T; lam=np.linalg.lstsq(A_,-g[idx],rcond=None)[0]; return np.linalg.norm(g[idx]+A_@lam)
            cls=[]; ex=''
            for trial in range(16):
                c=rng.normal(size=kgen)+1j*rng.normal(size=kgen); c=c/(lin@c)
                for it in range(60):
                    r_=np.concatenate([qres(c),[lin@c-1]]); J=np.empty((len(r_),kgen),complex); h=1e-7
                    for a_ in range(kgen):
                        cp=c.copy(); cp[a_]+=h; J[:,a_]=(np.concatenate([qres(cp),[lin@cp-1]])-r_)/h
                    dc=np.linalg.lstsq(J,-r_,rcond=None)[0]; c=c+dc
                    if np.linalg.norm(dc)<1e-12: break
                rr=np.linalg.norm(qres(c))/max(1,np.linalg.norm(c))**2
                if rr>1e-8: continue
                g=c@Kc; ng=np.linalg.norm(g); tol=1e-6*ng
                if any(resid_in(g,[k for k in range(2*L) if k not in (i,L+i)])<tol for i in range(L)): cls.append('one'); continue
                if resid_in(g,list(range(L)))<tol or resid_in(g,list(range(L,2*L)))<tol: cls.append('line'); continue
                cls.append('gen')
                # rank one mod gauge?  x + y in span of (gauge_x + gauge_y)  <=>  G = (e_P - e_Q) (x) x' after a gauge change
                zv=g[:L]+g[L:]
                if len(Gm):
                    A_=(Gm[:,:L]+Gm[:,L:]).T; lam=np.linalg.lstsq(A_,-zv,rcond=None)[0]; zr=np.linalg.norm(zv+A_@lam)
                else: zr=np.linalg.norm(zv)
                if zr<tol: cls[-1]='gen-r1'
                if os.environ.get('DBG'): print('DBG |Lm g| = %.1e  |q(g)| = %.1e  |Lm Gm^T| = %.1e |Lm Kc^T| = %.1e'%(np.linalg.norm(Lm@g),np.linalg.norm(qres(c)),np.linalg.norm(Lm@Gm.T) if len(Gm) else 0,np.linalg.norm(Lm@Kc.T)),flush=True)
                if os.environ.get('DUMP') and cls.count('gen')+cls.count('gen-r1')<=3:
                    Bm=[]
                    for (r_,v_) in rowel:
                        m_=np.zeros((4,5),complex); m_[r_]=[val[x] if x else 0 for x in v_]; Bm.append(m_)
                    for (c_,v_) in colel:
                        m_=np.zeros((4,5),complex); m_[:,c_]=[val[x] if x else 0 for x in v_]; Bm.append(m_)
                    m_=np.zeros((4,5),complex)
                    if kind=='row': m_[P]=g[:L]; m_[Q]=g[L:]
                    else: m_[:,P]=g[:L]; m_[:,Q]=g[L:]
                    Bm.append(m_)
                    nm=(tag.replace('TYPE ','').replace('|','_').replace(' ','_').replace('(','').replace(')','').replace(',',''))+'_%s_c%d_s%d.npy'%(''.join(map(str,bits)),len(kerdims),len(cls))
                    np.save('/home/kevxhk/work/L-gct-210/reg2/e5/dump/'+nm,np.array(Bm))
                if not ex: ex=''.join('1' if abs(t)>1e-6*ng else '0' for t in g)
            kerdims.append(('Q',kgen,'gen%d'%(cls.count('gen')+cls.count('gen-r1')),'rk1:%d'%cls.count('gen-r1'),'one%d'%cls.count('one'),'line%d'%cls.count('line'),'fail%d'%(16-len(cls)),ex))
            continue
        if os.environ.get('ZTEST') and kind=='row':
            # round 18: add z = x + y = 0 (G = (e_r - e_j) (x) x); compare kernel dimensions
            Z=np.zeros((L,len(gidx))); Z[:,:L]=np.eye(L); Z[:,L:]=np.eye(L)
            sv2=np.linalg.svd(np.concatenate([Lm,Z]),compute_uv=False); rk2=int((sv2>1e-8*max(1,sv2[0])).sum())
            kerdims.append((len(gidx)-rk,len(gidx)-rk2))
        else: kerdims.append(len(gidx)-rk)
    print('CLASS',tag,''.join(map(str,bits)),kerdims,flush=True)
    key='kernel dims %s'%kerdims
    out.setdefault('LINEAR-GENERIC-KILL' if all(k==0 for k in kerdims) else ('QUAD-GENERIC-KILL' if all(isinstance(k,tuple) and (k[0] in ('Q0','Qs0') or (k[0]=='Q' and k[2]=='gen0')) for k in kerdims) else key),[]).append(''.join(map(str,bits)))
print(tag+': %d classes -> '%len(classes)+'; '.join('%s x%d'%(k,len(v)) for k,v in sorted(out.items())),flush=True)
