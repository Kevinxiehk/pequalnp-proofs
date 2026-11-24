import itertools, random
PERMS=[(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]   # order of permanent_three
VARS=['a0','a1','a2','c0','c1','c2']
def ent(M,i,j): return "%s (%d, %d)"%(M,i,j)
def uentry(i,j,args,zero):
    a=args[i]; c=args[3+j]
    W = "0" if ('W',i,j) in zero else ent('W',i,j)
    Y = "0" if ('Y',i,j) in zero else ent('Y',i,j)
    B = "0" if ('b',i,j) in zero else ent('b',i,j)
    return "(%s + %s * %s + %s * %s)"%(B,a,W,c,Y)
def Ptext(args,zero):
    return " + ".join(" * ".join(uentry(i,s[i],args,zero) for i in range(3)) for s in PERMS)
def pmtext(zero=frozenset()):
    return " + ".join(" * ".join(("0" if ('b',i,s[i]) in zero else ent('b',i,s[i])) for i in range(3)) for s in PERMS)
def coef_monos(S,zero):
    """coefficient of prod of vars in S: list of monomials (list of entry texts)"""
    res=[]
    for s in PERMS:
        mono=[]; ok=True
        used=set()
        for i in range(3):
            j=s[i]
            wa = ('a%d'%i) in S
            wc = ('c%d'%j) in S
            if wa and wc: ok=False; break
            if wa: e=('W',i,j); used.add('a%d'%i)
            elif wc: e=('Y',i,j); used.add('c%d'%j)
            else: e=('b',i,j)
            mono.append(e)
        if not ok: continue
        if used!=set(S): continue
        if any(e in zero for e in mono): continue
        res.append(mono)
    return res
def coef_text(S,zero):
    ms=coef_monos(S,zero)
    if not ms: return "0"
    return " + ".join(" * ".join(ent(*e) for e in m) for m in ms)
def cert(S):
    S=list(S); terms=[]
    for r in range(1,len(S)+1):
        for T in itertools.combinations(S,r):
            sign = '+' if (len(S)-len(T))%2==0 else '-'
            args=" ".join('1' if v in T else '0' for v in VARS)
            terms.append("%s hexp %s"%(sign,args))
    t=" ".join(terms)
    return t[2:] if t.startswith('+ ') else t
def numcheck(S,zero,trials=3):
    random.seed(7)
    for _ in range(trials):
        val={}
        for M in 'bWY':
            for i in range(3):
                for j in range(3):
                    val[(M,i,j)] = 0 if (M,i,j) in zero else complex(random.gauss(0,1),random.gauss(0,1))
        def P(args):
            tot=0
            for s in PERMS:
                pr=1
                for i in range(3):
                    j=s[i]
                    pr*= val[('b',i,j)]+args[i]*val[('W',i,j)]+args[3+j]*val[('Y',i,j)]
                tot+=pr
            return tot
        P0=P([0]*6)
        tot=0
        Sl=list(S)
        for r in range(1,len(Sl)+1):
            for T in itertools.combinations(Sl,r):
                sign = 1 if (len(Sl)-len(T))%2==0 else -1
                tot+= sign*(P([1 if v in T else 0 for v in VARS])-P0)
        ex=0
        for m in coef_monos(S,zero):
            pr=1
            for e in m: pr*=val[e]
            ex+=pr
        if abs(tot-ex)>1e-9: return False
    return True
def have_coef(name,S,zero):
    assert numcheck(S,zero), (name,S)
    return "  have %s : %s = 0 := by\n    linear_combination %s"%(name,coef_text(S,zero),cert(S))
def hexp_block(zero, zero_names):
    args=VARS
    s ="  have hexp : ∀ a0 a1 a2 c0 c1 c2 : ℂ,\n      %s =\n        %s := by\n"%(Ptext(args,zero),pmtext())
    s+="    intro a0 a1 a2 c0 c1 c2\n    have t := bad_expand h a0 a1 a2 c0 c1 c2\n"
    if zero_names:
        s+="    rw [%s] at t\n"%(", ".join(zero_names))
    s+="    exact t"
    return s
if __name__=="__main__":
    z4={('W',0,1),('W',0,2)}
    print("X4c:",coef_text(['a0','a1','c2'],z4))
    z3={('W',0,1),('W',0,2),('W',1,0),('W',1,2)}
    for S in [['a0','a1'],['a0','a1','a2'],['a0','a1','c2'],['a0'],['a0','a2'],['a0','c2'],['a0','a2','c2'],['a1'],['a1','a2'],['a1','c2'],['a1','a2','c2'],['c2']]:
        print("X3c",S,":",coef_text(S,z3), numcheck(S,z3))
    z1={('Y',1,0),('Y',2,0),('Y',1,1),('Y',2,1)}
    for S in [['a1'],['a1','c0'],['a1','c1'],['a1','a2'],['a1','a2','c0'],['a1','a2','c1']]:
        print("X1c",S,":",coef_text(S,z1), numcheck(S,z1))
