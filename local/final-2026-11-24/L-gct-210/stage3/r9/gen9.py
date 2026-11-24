# Round 9 (stage3): F4b after the moment classification. Column k0 = 0 carries (1,1,1,1) in the y-rows, p = -e_0 + p', w_0 = 0.
# y_r = e_0 + u_r.  Cases:  C1G  : u_a = unknown zero-sum vector on columns 1..4 (u_b = u_c = u_d = 0), p', w unknown (zero-sum on 1..4);
#                                 with RAB=1 a Rabinowitsch variable forces u_a1 != 0 (S_4 on columns 1..4), RAB=0: u_a free (calibration).
#                         C12ab / C12ac : u_a = al (e_1 - e_2), u_b (resp. u_c) = be (e_3 - e_4), al, be != 0, w = e_1+e_2-e_3-e_4, p' = 0.
#                         C3b / C3c : u_a = c(-e_1-e_2+e_3+e_4), u_b (resp. u_c) = yy (e_1 - e_2), c, yy != 0, w = e_3 - e_4, p' = 0.
# g_a, g_c with entry 0 equal to 0 (gauge G_ab + beta (x^{ae} - x^{be})), chart g_{a,i} = 1, g_{c,k} = 1 (i, k in 1..4); g_b, g_d free.
# MODE: LEVEL = all coefficients of perm(J+m) - 120 in (c_a..c_d, mu, ga, de);  FULL = LEVEL + (i), (ii), (iii) in A_4.
import sys, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G
PARN=['ca','cb','cc','cd','mu','ga','de']
def build(case,chart,p,mode,rab=1,nd=0,strat=0):
    names=list(PARN)
    def new(n): names.append(n); return len(names)-1
    if nd: chart,(ib,id_)=chart[:-2],chart[-2:]
    if case=='C1G':
        iw,ia,ic=chart
        U=[new('u%d'%i) for i in range(3)]; Wv=[new('w%d'%i) for i in range(3) if i!=iw]; Pv=[new('pp%d'%i) for i in range(3) if i!=iw]
        tu=new('tu') if rab else None
    elif case in ('C12ab','C12ac'):
        ia,ic=chart; A1=new('al'); B1=new('be'); ta=new('ta'); tb=new('tb')
    elif case in ('C3b','C3c'):
        ia,ic=chart; A1=new('c'); B1=new('yy'); ta=new('ta'); tb=new('tb')
    ga_=[new('ga%d'%i) for i in range(1,5) if i!=ia]; gb_=[new('gb%d'%i) for i in range(5)]
    gc_=[new('gc%d'%i) for i in range(1,5) if i!=ic]; gd_=[new('gd%d'%i) for i in range(5)]
    if nd: TNB=new('tnb'); TND=new('tnd')
    G.setup(p,len(names)); V=G.var; C=G.const; one=C(1); zero={}
    e0=[one,zero,zero,zero,zero]
    def vsum(vs): return G.lin([(1,v) for v in vs])
    extra=[]
    if case=='C1G':
        u=[V(i) for i in U]; u.append(G.lin([(-1,x) for x in u])); ua=[zero]+u
        wl=[]; it=iter(Wv)
        for i in range(3): wl.append(one if i==iw else V(next(it)))
        wl.append(G.lin([(-1,x) for x in wl])); w=[zero]+wl
        pl=[]; it=iter(Pv)
        for i in range(3): pl.append(zero if i==iw else V(next(it)))
        pl.append(G.lin([(-1,x) for x in pl])); pp=[zero]+pl
        ys=[[G.add(e0[j],ua[j]) for j in range(5)],e0,e0,e0]
        pv=[G.sub(pp[j],e0[j]) for j in range(5)]
        if rab: extra.append(G.sub(G.mul(V(tu),u[0]),one))
    else:
        a,b=V(A1),V(B1)
        if case.startswith('C12'):
            ua=[zero,a,G.scal(-1,a),zero,zero]; ub=[zero,zero,zero,b,G.scal(-1,b)]
            w=[zero,one,one,C(-1),C(-1)]
        else:
            ua=[zero,G.scal(-1,a),G.scal(-1,a),a,a]; ub=[zero,b,G.scal(-1,b),zero,zero]
            w=[zero,zero,zero,one,C(-1)]
        ys=[[G.add(e0[j],ua[j]) for j in range(5)],e0,e0,e0]
        k=1 if case.endswith('b') else 2
        ys[k]=[G.add(e0[j],ub[j]) for j in range(5)]
        pv=[G.scal(-1,e0[j]) for j in range(5)]
        extra.append(G.sub(G.mul(V(ta),a),one)); extra.append(G.sub(G.mul(V(tb),b),one))
    def gvec(lst,ichart,free0):
        out=[]; it=iter(lst)
        for i in range(5):
            if not free0 and i==0: out.append(zero)
            elif not free0 and i==ichart: out.append(one)
            else: out.append(V(next(it)))
        return out
    ga=gvec(ga_,ia,False); gb=gvec(gb_,None,True); gc=gvec(gc_,ic,False); gd=gvec(gd_,None,True)
    if nd:   # (y_b, g_b) and (y_d, g_d) independent: the 2x2 minor on columns (0, ib) resp. (0, id) is invertible (y_r0 = 1)
        extra.append(G.sub(G.mul(V(TNB),G.sub(gb[ib],G.mul(ys[1][ib],gb[0]))),one))
        extra.append(G.sub(G.mul(V(TND),G.sub(gd[id_],G.mul(ys[3][id_],gd[0]))),one))
    ca,cb,cc,cd,mu,gA,dE=[V(i) for i in range(7)]; sig=vsum([ca,cb,cc,cd])
    M=[[G.lin([(1,one),(1,G.mul(ca,ys[0][j])),(1,G.mul(gA,ga[j]))]) for j in range(5)],
       [G.lin([(1,one),(1,G.mul(cb,ys[1][j])),(1,G.mul(gA,gb[j]))]) for j in range(5)],
       [G.lin([(1,one),(1,G.mul(cc,ys[2][j])),(1,G.mul(dE,gc[j]))]) for j in range(5)],
       [G.lin([(1,one),(1,G.mul(cd,ys[3][j])),(1,G.mul(dE,gd[j]))]) for j in range(5)],
       [G.lin([(1,one),(1,G.mul(sig,pv[j])),(1,G.mul(mu,w[j]))]) for j in range(5)]]
    f=G.sub(G.perm(M),C(120))
    eqs=[v for k,v in G.coeffs(f,list(range(7))).items() if v]
    nlev=len(eqs)
    if mode=='FULL':
        P={0:(ys[0],ga),1:(ys[1],gb),2:(ys[2],gc),3:(ys[3],gd)}; Pe=(w,pv)
        for ch in itertools.product(range(2),repeat=4):
            eqs+=list(G.subperms([P[r][ch[r]] for r in range(4)],4,5).values())
        for (s1,s2,t1,t2) in ((0,1,2,3),(2,3,0,1)):          # (ii): y_a, y_b kill P_c P_d P_e ; (iii): y_c, y_d kill P_a P_b P_e
            for s in (s1,s2):
                for ch in itertools.product(range(2),repeat=3):
                    eqs+=list(G.subperms([ys[s],P[t1][ch[0]],P[t2][ch[1]],Pe[ch[2]]],4,5).values())
    if strat:   # stratified cover: the chart coordinate is the FIRST nonzero one (earlier coordinates / minors vanish)
        if case=='C1G':
            for i in range(iw): eqs.append(wl[i])
        for j in range(1,ic): eqs.append(gc[j])
        for j in range(1,ia): eqs.append(ga[j])
        if nd:
            for j in range(1,ib): eqs.append(G.sub(gb[j],G.mul(ys[1][j],gb[0])))
            for j in range(1,id_): eqs.append(G.sub(gd[j],G.mul(ys[3][j],gd[0])))
    eqs+=extra
    eqs=[e for e in eqs if e]
    use=list(range(7,len(names)))
    return names,eqs,use,nlev
def charts(case,nd=0):
    # C1G: the system is invariant under S_4 on columns 1..4 and g_a != 0 on them, so the charts g_{a,1} = 1 cover everything
    base=list(itertools.product(range(3),[1],range(1,5))) if case=='C1G' else list(itertools.product(range(1,5),range(1,5)))
    if nd: base=[b+t for b in base for t in itertools.product(range(1,5),range(1,5))]
    return base
if __name__=='__main__':
    import time
    p=int(sys.argv[1]); case=sys.argv[2]; mode=sys.argv[3]; rab=int(sys.argv[4]) if len(sys.argv)>4 else 1
    nd=int(sys.argv[5]) if len(sys.argv)>5 else 0
    only=sys.argv[6] if len(sys.argv)>6 else None
    t0=time.time(); res={}; nl=None
    for ch in charts(case,nd):
        if only and ''.join(map(str,ch))!=only: continue
        names,eqs,use,nlev=build(case,ch,p,mode,rab,nd); nl=nlev
        path='/home/kevxhk/work/L-gct-210/stage3/r9/gb/%s_%s_r%d_n%d_%d_%s.ms'%(case,mode,rab,nd,p,''.join(map(str,ch)))
        G.write_ms(path,names,eqs,use); r,body=G.msolve(path,timeout=600); res[ch]=r
        if r!='unit': print(ch,'NONUNIT',r,body.replace('\n',' ')[:600],flush=True)
    print('prime',p,'case',case,'mode',mode,'rab',rab,'nd',nd,': charts',len(res),' level eqs',nl,' unit',sum(1 for v in res.values() if v=='unit'),
          ' non-unit',sum(1 for v in res.values() if v!='unit'),' time %.1f s'%(time.time()-t0),flush=True)
