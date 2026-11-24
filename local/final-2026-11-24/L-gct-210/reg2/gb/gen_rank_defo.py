# gen_rank certificate for a SKEW-DEFORMED family (NOTES-reg2 15.4).  usage: gen_rank_defo.py FAMILY kind idx tgt r K SEED [rel1;rel2;...]
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
fam,kind,idx,tgt,r,K,seed=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),sys.argv[5],sys.argv[6],sys.argv[7]
extra=[]; FIX={}; OMEGA=[]; DEFO2=None; ONLOC={}
for a in sys.argv[8:]:
    if a.startswith('defo2='):
        k2,i2,t2_=a[6:].split(','); DEFO2=(k2,int(i2),int(t2_))
    elif a.startswith('num='):              # round 10: num=name:complex value (on-locus point for the minor selection, with w = exp(2 pi i/3))
        ONLOC={}
        for kv in a[4:].split(','):
            k_,v_=kv.split(':'); ONLOC[k_]=v_
    elif a.startswith('fix='):
        for kv in a[4:].split(','):
            k,v=kv.split(':')
            if v=='omega': OMEGA.append(k)
            else: FIX[k]=v
    else: extra+=[x for x in a.split(';') if x]
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read()
cut=src.index('F=Family(params,bfn,d)')
sys.argv=['x',fam,r,K,seed]
exec(src[:cut])
base_bfn=bfn; base_params=list(params)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def dotv(a,b):
    t={}
    for x,y in zip(a,b):
        if x and y: t=add(t,mul(x,y))
    return t
from fractions import Fraction as _Fr
def bfn(R,V0):
    def V(n):
        if n in FIX and 'w' in FIX[n]:          # round 10: a value alpha + beta*w in Q(w) (w = the omega parameter, rel w^2+w+1)
            import sympy as _sp2
            _e=_sp2.Poly(_sp2.sympify(FIX[n]),_sp2.Symbol('w')); _c=dict(_e.terms()); _r={}
            for (_k,),_v in _c.items():
                _m=R.const(_Fr(str(_v)))
                for _ in range(_k): _m=mul(_m,V0('w'))
                _r=add(_r,_m)
            return _r
        if n in FIX:
            f=_Fr(FIX[n]); return R.const(f) if f!=0 else {}
        return V0(n)
    Bs=base_bfn(R,V); t=V('t')
    import math
    for B in Bs:
        dens=[_Fr(v).denominator for row in B for e in row if e for v in e.values()]
        L=1
        for dd in dens: L=L*dd//math.gcd(L,dd)
        for i in range(4):
            for j in range(5):
                if B[i][j]: B[i][j]={k:int(_Fr(v)*L) for k,v in B[i][j].items()}
    def _apply(Bs,kind,idx,tgt,t,grp):
        v=[[Bs[g][i][idx] for i in range(4)] if kind=='col' else [Bs[g][idx][j] for j in range(5)] for g in grp]
        g11=dotv(v[0],v[0]); g12=dotv(v[0],v[1]); g22=dotv(v[1],v[1])
        Jv=[[add(mul(g12,v[0][k]) if v[0][k] else {}, mul(g11,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))],
            [add(mul(g22,v[0][k]) if v[0][k] else {}, mul(g12,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))]]
        for n,g in enumerate(grp):
            for k in range(len(v[0])):
                if Jv[n][k]:
                    if kind=='col': Bs[g][k][tgt]=add(Bs[g][k][tgt],mul(t,Jv[n][k])) if Bs[g][k][tgt] else mul(t,Jv[n][k])
                    else: Bs[g][tgt][k]=add(Bs[g][tgt][k],mul(t,Jv[n][k])) if Bs[g][tgt][k] else mul(t,Jv[n][k])
    grp1=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
    grp2=None
    if DEFO2:
        k2,i2,tg2=DEFO2; grp2=[k for k,B in enumerate(Bs) if (support(B)[1]=={i2} if k2=='col' else support(B)[0]=={i2})]
    _apply(Bs,kind,idx,tgt,t,grp1)
    if DEFO2: _apply(Bs,k2,i2,tg2,V('t2'),grp2)
    return Bs
params=[p for p in base_params if p not in FIX]+['t']+(['t2'] if DEFO2 else []); rels=list(rels)+extra+['%s^2+%s+1'%(o,o) for o in OMEGA]
exec(src[cut:])
