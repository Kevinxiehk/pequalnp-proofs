# X4 generator (rows, round 6): strongly level 4x5 matrices / planes in WALSH coordinates -> Singular script (Groebner + saturation mod p).
#   usage: python3 x4gen.py P CASE OUT
#   CASE = A   : ONE matrix, five columns free (15 unknowns x_{a,p}); saturate by the 5 column ideals.   claim: unit ideal
#          A4  : ONE matrix, column 5 = 0, four columns free (12 unknowns); saturate by 4 column ideals. calibration: NON-unit
#          B   : PLANE s*h + t*h', column 5 = 0, row sums sigma(h) = (1,0,u), sigma(h') = (0,1,v) in Walsh coordinates,
#                columns 1..3 free, column 4 = sigma - (1+2+3)  (20 unknowns); saturate by the 4 column ideals.  claim: unit
#          B3  : as B with column 4 = 0 as well (column 3 = sigma - (1+2); 14 unknowns); saturate by 3 column ideals. calibration: NON-unit
#          C   : PLANE, five columns, columns 1..4 free, column 5 = sigma - sum (26 unknowns); saturate by the 5 column ideals.
# A column h_a of the 4x5 matrix is sum_p x_{a,p} chi_p, chi = rows of H^T (so every column sum is 0).
# Equations: all coefficients in the scaling parameters (s, or s,t) of  C_j(Y) - 24,  C_j = perm(J + Y without column j), j = 0..4.
import sys, itertools
p=int(sys.argv[1]); case=sys.argv[2]; out=sys.argv[3]
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
names=[]
def newvar(n): names.append(n); return len(names)-1
plane = case in ('B','B3','C')
nfree = {'A':5,'A4':4,'B':3,'B3':2,'C':4}[case]
ncols = {'A':5,'A4':4,'B':4,'B3':3,'C':5}[case]
X=[[newvar('x%d%d'%(a,q)) for q in range(3)] for a in range(nfree)]
Xp=[[newvar('y%d%d'%(a,q)) for q in range(3)] for a in range(nfree)] if plane else None
if plane: U=newvar('u'); Vv=newvar('v')
S=newvar('s'); T=newvar('t') if plane else None
NV=len(names)
def mono(i):
    e=[0]*NV; e[i]=1; return tuple(e)
ZERO=tuple([0]*NV)
def add(a,b,c=1):
    r=dict(a)
    for k,v in b.items():
        w=(r.get(k,0)+c*v)%p
        if w: r[k]=w
        elif k in r: del r[k]
    return r
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)%p
    return {k:v for k,v in r.items() if v}
def lin(pairs):   # sum c_i * var_i
    r={}
    for c,i in pairs:
        if c%p: r=add(r,{mono(i):c%p})
    return r
# Walsh coordinate vectors (as polynomials) of the columns of h and h'
def colcoords(Xv,sig):
    cols=[[lin([(1,Xv[a][q])]) for q in range(3)] for a in range(nfree)]
    if case in ('B','B3','C'):      # last active column = sigma - sum of the free ones
        last=[add(sig[q],{}) for q in range(3)]
        for a in range(nfree):
            for q in range(3): last[q]=add(last[q],cols[a][q],-1)
        cols.append(last)
    while len(cols)<5: cols.append([{},{},{}])
    return cols
one={ZERO:1}
if plane:
    sig =[one,{},lin([(1,U)])]; sigp=[{},one,lin([(1,Vv)])]
    Ch=colcoords(X,sig); Chp=colcoords(Xp,sigp)
else:
    Ch=colcoords(X,None); Chp=None
# 4x5 matrix Y (entries: polynomials), Y[i][a] = s*sum_q H[i][q] Ch[a][q] (+ t * ...)
sv={mono(S):1}; tv={mono(T):1} if plane else None
Y=[[None]*5 for _ in range(4)]
for i in range(4):
    for a in range(5):
        e={}
        for q in range(3): e=add(e,Ch[a][q],H[i][q])
        e=mul(sv,e)
        if plane:
            f={}
            for q in range(3): f=add(f,Chp[a][q],H[i][q])
            e=add(e,mul(tv,f))
        Y[i][a]=e
def Cj(j):
    cols=[c for c in range(5) if c!=j]; tot={}
    M=[[add(one,Y[i][c]) for c in cols] for i in range(4)]
    # permanent by Laplace expansion with memo over column subsets
    memo={}
    def pr(i,mask):
        if i==4: return one
        key=(i,mask)
        if key in memo: return memo[key]
        r={}
        for c in range(4):
            if not (mask>>c)&1: r=add(r,mul(M[i][c],pr(i+1,mask|(1<<c))))
        memo[key]=r; return r
    return add(pr(0,0),{ZERO:(-24)%p})
eqs=[]
for j in range(5):
    C=Cj(j); parts={}
    for k,v in C.items():
        key=(k[S],k[T]) if plane else (k[S],)
        kk=list(k); kk[S]=0
        if plane: kk[T]=0
        parts.setdefault(key,{})[tuple(kk)]=v
    for key,pol in sorted(parts.items()):
        assert sum(key)>0, 'constant term'
        if pol: eqs.append(pol)
uvars=[n for n in names if n not in ('s','t')]
def show(pol):
    terms=[]
    for k,v in sorted(pol.items()):
        m='*'.join('%s^%d'%(names[i],e) if e>1 else names[i] for i,e in enumerate(k) if e and names[i] not in ('s','t'))
        terms.append('%d%s'%(v,'*'+m if m else ''))
    return '+'.join(terms) if terms else '0'
# column ideals for saturation
def colideal(a):
    gens=[show(Ch[a][q]) for q in range(3)]
    if plane: gens+=[show(Chp[a][q]) for q in range(3)]
    return [g for g in gens if g!='0']
with open(out,'w') as f:
    f.write('ring r=%d,(%s),dp;\noption(redSB);\nLIB "elim.lib";\n'%(p,','.join(uvars)))
    f.write('ideal I=\n'+',\n'.join(show(e) for e in eqs)+';\n')
    f.write('int t0=timer; I=std(I);\nprintf("case %s p=%d: %d equations, %d unknowns; dim of the ideal (affine) = %%s, basis size %%s",dim(I),size(I));\n'%(case,p,len(eqs),len(uvars)))
    for a in range(ncols):
        f.write('ideal J%d=%s;\nI=sat(I,J%d);\nprintf("  after saturation by column %d: basis size %%s, dim %%s, unit: %%s",size(I),dim(I),(reduce(1,I)==0));\n'%(a,','.join(colideal(a)),a,a))
    f.write('printf("RESULT case %s p=%d: %%s",(reduce(1,std(I))==0));\nquit;\n'%(case,p))
# optional msolve output with Rabinowitsch localisation: argv[4] = chart string, one character per active column:
#   digit k = k-th generator of that column ideal must be nonzero, 'r' = a fixed pseudo-random linear combination of the generators, '-' = no condition
if len(sys.argv)>4:
    import random
    chart=sys.argv[4]; rnd=random.Random(12345+p%1000)
    extra=[]; zn=[]
    for a,ch in enumerate(chart):
        if ch=='-': continue
        gens=[Ch[a][q] for q in range(3)]+([Chp[a][q] for q in range(3)] if plane else [])
        gens=[g for g in gens if g]
        if ch=='r':
            g={}
            for h in gens: g=add(g,h,rnd.randrange(1,p))
        else: g=gens[int(ch)]
        extra.append(g); zn.append('z%d'%a)
    with open(out+'.ms','w') as f:
        f.write(','.join(uvars+zn)+'\n%d\n'%p)
        pols=[show(e) for e in eqs]+['(%s)*%s-1'%(show(g),z) for g,z in zip(extra,zn)]
        f.write(',\n'.join(pols)+'\n')
    print('written',out+'.ms','with',len(extra),'localisations')
print('written',out,'equations',len(eqs),'unknowns',len(uvars))
