# Round 10: X0 = Y_ab (+) Y_cd (the 4-dim core of normal form (t2)): Y_ab = {(v, phi v)}, Y_cd = {(u, psi u)} 2-dim 2-row level spaces with
# phi, psi injective. x = (al v1 + be v2, al b1 + be b2, ga u1 + et u2, ga d1 + et d2). P_a in Schubert form with pivots (0,1) (S_5),
# P_c Schubert with pivots (k1,k2) (10 charts); injectivity of phi, psi: Rabinowitsch on the Pluecker coordinate (mb) of (b1,b2), (md) of (d1,d2).
import sys, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G
PRS=list(itertools.combinations(range(5),2))
def schubert(vars_,piv,V,one,zero):
    rest=[j for j in range(5) if j not in piv]; it=iter(vars_); r1=[None]*5; r2=[None]*5
    r1[piv[0]]=one; r1[piv[1]]=zero; r2[piv[0]]=zero; r2[piv[1]]=one
    for j in rest:
        r1[j]=V(next(it)); r2[j]=V(next(it))
    for j in range(5):                       # Schubert normal form: entries left of the pivot vanish
        if j<piv[0]: r1[j]=zero
        if j<piv[1] and j not in piv: pass
    return r1,r2
def build(chart,p):
    kc,mb,md=chart; names=['al','be','ga','et']
    def new(n): names.append(n); return len(names)-1
    A=[new('a%d'%i) for i in range(6)]; B1=[new('b%d'%j) for j in range(5)]; B2=[new('c%d'%j) for j in range(5)]
    Cv=[new('g%d'%i) for i in range(6)]; D1=[new('d%d'%j) for j in range(5)]; D2=[new('f%d'%j) for j in range(5)]
    TB=new('tb'); TD=new('td')
    G.setup(p,len(names)); V=G.var; C=G.const; one=C(1); zero={}
    v1,v2=schubert(A,(0,1),V,one,zero); u1,u2=schubert(Cv,PRS[kc],V,one,zero)
    b1=[V(t) for t in B1]; b2=[V(t) for t in B2]; d1=[V(t) for t in D1]; d2=[V(t) for t in D2]
    al,be,ga,et=[V(t) for t in range(4)]
    def comb(x,y,p_,q_): return [G.lin([(1,G.mul(p_,x[j])),(1,G.mul(q_,y[j]))]) for j in range(5)]
    rows=[comb(v1,v2,al,be),comb(b1,b2,al,be),comb(u1,u2,ga,et),comb(d1,d2,ga,et)]
    M=[[G.add(one,r[j]) for j in range(5)] for r in rows]+[[one]*5]
    f=G.sub(G.perm(M),C(120)); eqs=[v for k,v in G.coeffs(f,list(range(4))).items() if v]; nlev=len(eqs)
    x,y=PRS[mb]; eqs.append(G.sub(G.mul(V(TB),G.sub(G.mul(b1[x],b2[y]),G.mul(b1[y],b2[x]))),one))
    x,y=PRS[md]; eqs.append(G.sub(G.mul(V(TD),G.sub(G.mul(d1[x],d2[y]),G.mul(d1[y],d2[x]))),one))
    return names,eqs,list(range(4,len(names))),nlev
def charts(): return [(kc,mb,md) for kc in range(10) for mb in range(10) for md in range(10)]
if __name__=='__main__':
    import time
    p=int(sys.argv[1]); only=sys.argv[2] if len(sys.argv)>2 else None; t0=time.time(); res={}
    for ch in charts():
        tag='%d_%d_%d'%ch
        if only and tag!=only: continue
        names,eqs,use,nlev=build(ch,p); path='/home/kevxhk/work/L-gct-210/stage3/r10/gb/x0_%d_%s.ms'%(p,tag)
        G.write_ms(path,names,eqs,use); r,body=G.msolve(path,timeout=1500); res[ch]=r
        print(tag,'unit' if r=='unit' else 'NONUNIT %s %s'%(r,body.replace('\n',' ')[:500]),'%.1f s'%(time.time()-t0),flush=True)
    print('X0 prime',p,'charts',len(res),'level eqs',nlev,'unit',sum(1 for v in res.values() if v=='unit'),flush=True)
