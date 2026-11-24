# Exact (mod p) test of configuration (a), sub-case (iv-2), see NOTES-ncol N2.3:
#   3-dim spaces Q of 4x4 matrices whose rows lie in a fixed plane U (perp 1), with (L2) g(r_i, sigma - r_i) == 0 (i = 0..3),
#   (L3) tau(r_k,r_l,r_m) == 0 (all triples), (L4) perm(q) == 0  identically on Q.   [= Q level + all row deletions level, rows in U]
# Q in Gr(3,8): coordinates (s_i, p_i) of the rows r_i = s_i u1 + p_i u2; Pluecker chart = pivot set of 3 coordinates; no saturation.
# usage: python3 -I iv2gen.py P MODE OUTDIR      MODE = iv2 (U = {sum 0, x0 = x1}) | cal (U = span(chi, u'), contains chi: NON-unit expected)
import sys, itertools, os
P=int(sys.argv[1]); MODE=sys.argv[2]; OUT=sys.argv[3]; os.makedirs(OUT,exist_ok=True)
def inv(a): return pow(a%P,P-2,P)
if MODE=='iv2': U=[[1,1,-2,0],[0,0,1,-1]]
else:
    I=None
    for a in range(2,10**6):
        c=pow(a,(P-1)//4,P)
        if c*c%P==P-1: I=c; break
    U=[[1,I,P-1,P-I],[1,0,0,P-1]]          # chi = (1,i,-1,-i), u' = e_0 - e_3
U=[[x%P for x in u] for u in U]
NV=18   # vars: phi0..2 (0..2), m0..14 (3..17)
def padd(a,b):
    c=dict(a)
    for k,v in b.items():
        w=(c.get(k,0)+v)%P
        if w: c[k]=w
        elif k in c: del c[k]
    return c
def pmul(a,b):
    c={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); w=(c.get(k,0)+v1*v2)%P
            if w: c[k]=w
            else: c.pop(k,None)
    return c
def pscal(a,s): return {k:(v*s)%P for k,v in a.items() if (v*s)%P}
def var(i):
    e=[0]*NV; e[i]=1; return {tuple(e):1}
ONE={tuple([0]*NV):1}
def entries(coords):   # coords: list of 8 polys (s_0..s_3, p_0..p_3) -> 4x4 entries
    q=[[None]*4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            q[i][j]=padd(pscal(coords[i],U[0][j]),pscal(coords[4+i],U[1][j]))
    return q
def dot(a,b):
    r={}
    for j in range(4): r=padd(r,pmul(a[j],b[j]))
    return r
def gen_chart(piv):
    nonpiv=[c for c in range(8) if c not in piv]
    coords=[None]*8
    for k,c in enumerate(piv): coords[c]=var(k)
    mi=0
    for c in nonpiv:
        s={}
        for k in range(3): s=padd(s,pmul(var(k),var(3+mi))); mi+=1
        coords[c]=s
    q=entries(coords)
    rows=[q[i] for i in range(4)]
    sig=[{} for _ in range(4)]
    for j in range(4):
        for i in range(4): sig[j]=padd(sig[j],rows[i][j])
    eqs=[]
    for i in range(4):
        diff=[padd(sig[j],pscal(rows[i][j],P-1)) for j in range(4)]
        eqs.append(dot(rows[i],diff))
    for T in itertools.combinations(range(4),3):
        t={}
        for j in range(4): t=padd(t,pmul(pmul(rows[T[0]][j],rows[T[1]][j]),rows[T[2]][j]))
        eqs.append(t)
    r=rows; L4={}
    for (a,b,c,d) in [(0,1,2,3),(0,2,1,3),(0,3,1,2)]: L4=padd(L4,pmul(dot(r[a],r[b]),dot(r[c],r[d])))
    t={}
    for j in range(4): t=padd(t,pmul(pmul(r[0][j],r[1][j]),pmul(r[2][j],r[3][j])))
    L4=padd(L4,pscal(t,P-6)); eqs.append(L4)
    # coefficients w.r.t. phi monomials
    out={}
    for E in eqs:
        for k,v in E.items():
            key=(id(E),k[:3]); mk=k[3:]
            d=out.setdefault(key,{}); d[mk]=(d.get(mk,0)+v)%P
    polys=[]
    for key,d in out.items():
        terms=[]
        for mk,v in d.items():
            if v==0: continue
            mono='*'.join(('m%d^%d'%(i,e) if e>1 else 'm%d'%i) for i,e in enumerate(mk) if e)
            terms.append(str(v)+('*'+mono if mono else ''))
        if terms: polys.append('+'.join(terms))
    return polys
names=','.join('m%d'%i for i in range(15))
for piv in itertools.combinations(range(8),3):
    polys=gen_chart(list(piv)); tag=''.join(map(str,piv))
    with open(os.path.join(OUT,'%s_%s.ms'%(MODE,tag)),'w') as f:
        f.write(names+'\n%d\n'%P); f.write(',\n'.join(polys)+'\n')
print('wrote 56 charts to',OUT)
