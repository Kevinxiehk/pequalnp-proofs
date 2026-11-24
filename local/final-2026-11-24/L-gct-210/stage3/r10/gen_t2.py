# Round 10: (PR2) in normal form (t2) (section 16): L' = Y_ab (+) Y_cd (+) C(w;0;s;0), Y_ab = graph of phi: P_a -> P_b, Y_cd = graph of psi.
# Coordinates (al,be,ga,et,de):  row a = (al+de) w + be v2,  row b = al b1 + be b2,  row c = (ga + de*sg) sh + et u2,  row d = ga d1 + et d2.
# Gauge/symmetry: S_5 on columns gives w_0 != 0, scale w_0 = 1 (de-scaling); v2 = basis vector of P_a mod w with v2_0 = 0, S_4 on columns 1..4
# gives v2_1 != 0, scale v2_1 = 1 (GL_2 of P_a).  Chart (i,k): sh_i = 1 (s = sg*sh, sg != 0 by Rabinowitsch), u2_i = 0, u2_k = 1.
# MODE LEVEL: all coefficients of perm(J + (x;0)) - 120.  INJ=1 adds Rabinowitsch for phi, psi injective via minor charts (mb, md).
import sys, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G
PARN=['al','be','ga','et','de']
def build(chart,p,inj=0):
    if inj: i,k,mb,md=chart
    else: i,k=chart
    names=list(PARN)
    def new(n): names.append(n); return len(names)-1
    W=[new('w%d'%j) for j in range(1,5)]; V2=[new('v%d'%j) for j in range(2,5)]
    B1=[new('b%d'%j) for j in range(5)]; B2=[new('c%d'%j) for j in range(5)]
    SH=[new('s%d'%j) for j in range(5) if j!=i]; U2=[new('u%d'%j) for j in range(5) if j not in (i,k)]
    D1=[new('d%d'%j) for j in range(5)]; D2=[new('f%d'%j) for j in range(5)]
    SG=new('sg'); TS=new('ts')
    if inj: TB=new('tb'); TD=new('td')
    G.setup(p,len(names)); V=G.var; C=G.const; one=C(1); zero={}
    w=[one]+[V(t) for t in W]; v2=[zero,one]+[V(t) for t in V2]
    b1=[V(t) for t in B1]; b2=[V(t) for t in B2]; d1=[V(t) for t in D1]; d2=[V(t) for t in D2]
    it=iter(SH); sh=[one if j==i else V(next(it)) for j in range(5)]
    it=iter(U2); u2=[zero if j==i else (one if j==k else V(next(it))) for j in range(5)]
    al,be,ga,et,de=[V(t) for t in range(5)]; sg=V(SG)
    ra=[G.lin([(1,G.mul(G.add(al,de),w[j])),(1,G.mul(be,v2[j]))]) for j in range(5)]
    rb=[G.lin([(1,G.mul(al,b1[j])),(1,G.mul(be,b2[j]))]) for j in range(5)]
    rc=[G.lin([(1,G.mul(G.add(ga,G.mul(de,sg)),sh[j])),(1,G.mul(et,u2[j]))]) for j in range(5)]
    rd=[G.lin([(1,G.mul(ga,d1[j])),(1,G.mul(et,d2[j]))]) for j in range(5)]
    M=[[G.add(one,r[j]) for j in range(5)] for r in (ra,rb,rc,rd)]+[[one]*5]
    f=G.sub(G.perm(M),C(120))
    eqs=[v for kk,v in G.coeffs(f,list(range(5))).items() if v]
    nlev=len(eqs)
    eqs.append(G.sub(G.mul(V(TS),sg),one))
    if inj:
        pr=list(itertools.combinations(range(5),2))
        x,y=pr[mb]; eqs.append(G.sub(G.mul(V(TB),G.sub(G.mul(b1[x],b2[y]),G.mul(b1[y],b2[x]))),one))
        x,y=pr[md]; eqs.append(G.sub(G.mul(V(TD),G.sub(G.mul(d1[x],d2[y]),G.mul(d1[y],d2[x]))),one))
    return names,eqs,list(range(5,len(names))),nlev
def charts(inj=0):
    base=[(i,k) for i in range(5) for k in range(5) if k!=i]
    return [b+(mb,md) for b in base for mb in range(10) for md in range(10)] if inj else base
if __name__=='__main__':
    import time
    p=int(sys.argv[1]); inj=int(sys.argv[2]); only=sys.argv[3] if len(sys.argv)>3 else None
    t0=time.time(); res={}
    for ch in charts(inj):
        tag=''.join(map(str,ch))
        if only and tag!=only: continue
        names,eqs,use,nlev=build(ch,p,inj)
        path='/home/kevxhk/work/L-gct-210/stage3/r10/gb/t2_i%d_%d_%s.ms'%(inj,p,tag)
        G.write_ms(path,names,eqs,use); r,body=G.msolve(path,timeout=900); res[ch]=r
        print(tag,'unit' if r=='unit' else 'NONUNIT %s %s'%(r,body.replace('\n',' ')[:700]),'%.1f s'%(time.time()-t0),flush=True)
    print('t2 prime',p,'inj',inj,'charts',len(res),'level eqs',nlev,'unit',sum(1 for v in res.values() if v=='unit'),'time %.1f'%(time.time()-t0),flush=True)
