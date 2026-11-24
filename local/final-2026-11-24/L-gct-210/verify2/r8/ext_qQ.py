# verify2 r9: EXACT (mod p) extension test via second order at ALL base points.
# Any level L containing X lies in T' (first order); for L = X + span(y_1..y_k), the lam^2-part of perm(J + x + sum lam_i y_i) - 120 gives
#     q_x(y_i, y_j) = 0  for all x in X, all i <= j        (q_x = Hessian of perm at J + x; polynomial of degree <= 3 in x).
# Grassmannian Gr(k, T'/X) by Schubert cells (complete cover); equations = all x-coefficients; NO saturation, NO Rabinowitsch.
# The incidence variety is closed in a Grassmannian (proper), so UNIT in every cell at one prime => no (5+k)-dim level space contains X (char 0).
# usage: python3 -I ext_q.py NAME K [cells=all|i,j,..] [timeout=T]      (NAME from ext_T1.json or 'CAL' = 5-dim subspace of L080)
import sys, json, itertools, subprocess, time, os, random
P=0
name=sys.argv[1]; K=int(sys.argv[2]); opts=dict(a.split('=') for a in sys.argv[3:] if '=' in a); TMO=float(opts.get('timeout',600))
OUT='/home/kevxhk/work/L-gct-210/verify2/r8/extqQ'; os.makedirs(OUT,exist_ok=True)
D=json.load(open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1.json'))
X=D[name]['X']; U=D[name]['U']; n=len(U)
NX=5
def padd(a,b,c=1):
    r=dict(a)
    for k,v in b.items():
        x=(r.get(k,0)+c*v)
        if x: r[k]=x
        elif k in r: del r[k]
    return r
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)
    return {k:v for k,v in r.items() if v}
Z0=tuple([0]*NX)
def entry(a,b):   # 1 + sum x_q X_q[a,b]
    e={Z0:1}
    for q in range(NX):
        c=X[q][a*5+b]
        if c:
            k=[0]*NX; k[q]=1; e=padd(e,{tuple(k):c})
    return e
E=[[entry(a,b) for b in range(5)] for a in range(5)]
def perm3(rows,cols):
    tot={}
    for s in itertools.permutations(range(3)):
        t={Z0:1}
        for i in range(3): t=pmul(t,E[rows[i]][cols[s[i]]])
        tot=padd(tot,t)
    return tot
H={}
for (a,b),(c,d) in itertools.product(itertools.product(range(5),range(5)),repeat=2):
    if a!=c and b!=d and (a*5+b)<=(c*5+d):
        rows=[r for r in range(5) if r not in (a,c)]; cols=[r for r in range(5) if r not in (b,d)]
        H[(a*5+b,c*5+d)]=perm3(rows,cols)
def Hget(i,j): return H[(i,j)] if i<=j else H[(j,i)]
Q={}
for A in range(n):
    for B in range(A,n):
        tot={}
        for i in range(25):
            if U[A][i]==0: continue
            for j in range(25):
                if U[B][j]==0: continue
                if (i,j) in H or (j,i) in H: tot=padd(tot,Hget(i,j),U[A][i]*U[B][j])
        Q[(A,B)]=tot
def Qget(A,B): return Q[(A,B)] if A<=B else Q[(B,A)]
def cells(n,k): return list(itertools.combinations(range(n),k))
CL=cells(n,K)
sel=list(range(len(CL))) if opts.get('cells','all')=='all' else [int(c) for c in opts['cells'].split(',')]
res={}; t0=time.time()
for ci in sel:
    piv=CL[ci]; free=[(i,j) for i in range(K) for j in range(n) if j>piv[i] and j not in piv]; nc=len(free)
    cidx={f:t for t,f in enumerate(free)}
    # coefficient of u_A in y_i: polynomial in c (variables indexed 0..nc-1)
    def coeff(i,A):
        if A==piv[i]: return {tuple([0]*nc):1}
        if (i,A) in cidx:
            k=[0]*nc; k[cidx[(i,A)]]=1; return {tuple(k):1}
        return {}
    eqs=[]
    for i in range(K):
        for j in range(i,K):
            # sum_{A,B} coeff(i,A) coeff(j,B) Q_AB(x): combine as dict keyed (x-monomial) -> poly in c
            byx={}
            for A in range(n):
                ca=coeff(i,A)
                if not ca: continue
                for B in range(n):
                    cb=coeff(j,B)
                    if not cb: continue
                    cc=pmul(ca,cb)
                    for xm,v in Qget(A,B).items():
                        byx[xm]=padd(byx.get(xm,{}),{k:(w*v) for k,w in cc.items()})
            eqs+=[p for p in byx.values() if p]
    names=['c%d'%t for t in range(nc)]
    tag='%s_k%d_cell%03d'%(name,K,ci); fn='%s/%s.ms'%(OUT,tag)
    if any(len(p)==1 and tuple([0]*nc) in p for p in eqs): res[ci]='UNIT(const)'; continue
    if nc==0:
        res[ci]='UNIT(const)' if any(eqs) else 'NONUNIT(point)'; continue
    def fmt(p):
        ts=[]
        for k,v in p.items():
            m='*'.join('%s^%d'%(names[t],e) for t,e in enumerate(k) if e)
            ts.append('%d*%s'%(v,m) if m else '%d'%v)
        return '+'.join(ts)
    fn=fn.replace('.ms','.sing')
    with open(fn,'w') as f:
        f.write('ring r=0,(%s),dp;\nideal I=%s;\nideal G=std(I);\nif (size(G)==1 and G[1]==1) {"RES UNIT";} else {"RES NONUNIT",dim(G);}\nquit;\n'%(','.join(names),',\n'.join(fmt(p) for p in eqs)))
    try:
        o=subprocess.run(['/usr/bin/Singular','-q',fn],capture_output=True,text=True,timeout=TMO).stdout
        r=[l for l in o.splitlines() if l.startswith('RES')]; res[ci]=r[0].split()[1] if r else 'ERROR'
    except subprocess.TimeoutExpired: res[ci]='TIMEOUT'
    print(ci,piv,'nvars',nc,'neqs',len(eqs),res[ci],'%.1fs'%(time.time()-t0),flush=True)
vals=list(res.values())
print('SUMMARY %s k=%d n=%d: cells %d, UNIT %d, NONUNIT %d, other %d'%(name,K,n,len(vals),sum(v.startswith('UNIT') for v in vals),sum(v.startswith('NONUNIT') for v in vals),sum(not v.startswith('UNIT') and not v.startswith('NONUNIT') for v in vals)),flush=True)
