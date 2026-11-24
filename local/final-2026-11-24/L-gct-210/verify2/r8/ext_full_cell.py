# verify2 r9: add SAMPLED full level equations perm(J + x + sum lam_i y_i(c)) - 120 (random numeric (x, lam) mod p) to the q-system of one cell.
# Each sampled equation is a constant-coefficient combination of the true coefficient equations, so the new ideal is still inside the full one:
# UNIT => the cell contains no (5+k)-dim level space.   usage: python3 -I ext_full_cell.py NAME K CELL NSAMPLES
import sys, json, itertools, random, subprocess
P=2147483629
name,K,ci,ns=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
D=json.load(open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1.json')); X=D[name]['X']; U=D[name]['U']; n=len(U)
piv=list(itertools.combinations(range(n),K))[ci]
free=[(i,j) for i in range(K) for j in range(n) if j>piv[i] and j not in piv]; nc=len(free)
def padd(a,b,c=1):
    r=dict(a)
    for k,v in b.items():
        x=(r.get(k,0)+c*v)%P
        if x: r[k]=x
        elif k in r: del r[k]
    return r
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=(r.get(k,0)+v1*v2)%P
    return {k:v for k,v in r.items() if v}
Z=tuple([0]*nc)
random.seed(int(sys.argv[5]) if len(sys.argv)>5 else 1)
eqs=[]
for s in range(ns):
    x=[random.randrange(P) for _ in range(5)]; lam=[random.randrange(P) for _ in range(K)]
    A=[[None]*5 for _ in range(5)]
    for a in range(5):
        for b in range(5):
            idx=a*5+b; const=(1+sum(x[q]*X[q][idx] for q in range(5))+sum(lam[i]*U[piv[i]][idx] for i in range(K)))%P
            e={Z:const} if const else {}
            for t,(i,j) in enumerate(free):
                v=lam[i]*U[j][idx]%P
                if v: k=[0]*nc; k[t]=1; e=padd(e,{tuple(k):v})
            A[a][b]=e
    dp={0:{Z:1}}
    for a in range(5):
        nd={}
        for S,v in dp.items():
            for b in range(5):
                if S>>b&1 or not A[a][b]: continue
                T=S|1<<b; t=pmul(v,A[a][b]); nd[T]=padd(nd[T],t) if T in nd else t
        dp=nd
    pe=padd(dp.get(31,{}),{Z:120},-1)
    eqs.append(pe); print('sample',s,'terms',len(pe),flush=True)
names=['c%d'%t for t in range(nc)]
def fmt(p):
    ts=[]
    for k,v in p.items():
        m='*'.join('%s^%d'%(names[t],e) for t,e in enumerate(k) if e)
        ts.append('%d*%s'%(v,m) if m else '%d'%v)
    return '+'.join(ts) if ts else '0'
base='/home/kevxhk/work/L-gct-210/verify2/r8/extq/%s_k%d_cell%03d.ms'%(name,K,ci)
L=open(base).read().split('\n'); qpolys=[x.rstrip(',') for x in L[2:] if x.strip()]
fn=base.replace('.ms','_full%d.ms'%ns)
open(fn,'w').write(L[0]+'\n%d\n'%P+',\n'.join(qpolys+[fmt(p) for p in eqs if p])+'\n')
subprocess.run(['/usr/bin/msolve','-g','2','-f',fn,'-o',fn+'.gb'],capture_output=True,timeout=1200)
s=open(fn+'.gb').read(); body=''.join(l for l in s.splitlines() if not l.startswith('#')).replace(' ','')
print('VERDICT',name,'cell',ci,'with',ns,'sampled full equations:', 'UNIT' if body.strip().rstrip(':') in ('[1]','[1]:') else 'NONUNIT', [l for l in s.splitlines() if 'length' in l])
