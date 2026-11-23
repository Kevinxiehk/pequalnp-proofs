# EXACT/MODULAR test for the NC family M(w0,w1,w3) of NOTES-reg2 section 2.5:
#   claim: Omega(M) = span(1, e_0) for every member with w0, w1, w3 != 0   (then dim L <= 7 whenever L_r = M, criterion A).
# System: parameters a = w0, b = w1, c = w3 in C^4 (columns 1..4) with the 7 family relations and a chart a_ja = b_jb = c_jc = 1;
#   unknown t = (X ; rho) in T_1(M), normalised by rho_0 = 0, rho_1+..+rho_4 = 0 (subtract the known elements with row-r parts 1, e_0)
#   and rho_jr = 1.  Unit ideal in every chart  <=>  no first-order extension with rho outside span(1, e_0).
# usage: gen_nc.py PRIME [cal|e0]   (PRIME = 0: exact over Q with Singular)
# mode e0: rho = 0 and X normalised modulo M + C d (column 0 of X zero, x_{0,ja} = x_{1,jb} = x_{3,jc} = 0); 13 charts x_ib = 1.
import sys, itertools, time; sys.path.insert(0,"/home/claude/work/L-gct-210/reg2/gb")
from polylib import *
p=int(sys.argv[1]); cal=len(sys.argv)>2 and sys.argv[2]=='cal'; e0=len(sys.argv)>2 and sys.argv[2] in ('e0','e0cal'); e0cal=len(sys.argv)>2 and sys.argv[2]=='e0cal'
RUN=(lambda polys,names,p,tag: run_singular(polys,names,tag)) if p==0 else run_msolve
ys=['y%d'%i for i in range(1,7)]; av=['a%d'%i for i in range(1,5)]; bv=['b%d'%i for i in range(1,5)]; cv=['c%d'%i for i in range(1,5)]
xv=['x%d%d'%(i,j) for i in range(4) for j in range(5)]; rv=['r%d'%j for j in range(5)]
R=Ring(ys+av+bv+cv+xv+rv); V=R.var; one=R.const(1)
def lin(c0,terms):
    q=R.const(c0)
    for coef,pl in terms: q=add(q,pl,coef)
    return q
A=[[None]*5 for _ in range(5)]
A[0]=[lin(1,[(1,V('y1'))])]+[add(one,mul(V('y4'),V(a))) for a in av]
A[1]=[lin(1,[(1,V('y2'))])]+[add(one,mul(V('y5'),V(b))) for b in bv]
A[2]=[lin(1,[(-1,V('y1')),(-1,V('y2')),(-1,V('y3'))])]+[one]*4
A[3]=[lin(1,[(1,V('y3'))])]+[add(one,mul(V('y6'),V(c))) for c in cv]
A[4]=[one]*5
t0=time.time(); FO={}
for i in range(5):
    for j in range(5):
        cofm=perm4([[A[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i])
        tv=V('x%d%d'%(i,j)) if i<4 else V('r%d'%j)
        FO=add(FO,mul(cofm,tv))
co=coeffs_wrt(FO,R,ys); eqs=list(co.values())
# drop the y variables from the exponent tuples
ny=len(ys); names=R.names[ny:]
strip=lambda q:{k[ny:]:v for k,v in q.items()}
eqs=[strip(q) for q in eqs]
R2=Ring(names); W=R2.var
def dot(u,v):
    q={}
    for s,t in zip(u,v): q=add(q,mul(W(s),W(t)))
    return q
def sm(u):
    q={}
    for s in u: q=add(q,W(s))
    return q
tri={}
for s,t,u in zip(av,bv,cv): tri=add(tri,mul(mul(W(s),W(t)),W(u)))
fam=[sm(av),sm(bv),sm(cv),dot(av,bv),dot(av,cv),dot(bv,cv),tri]
print('FO equations: %d (generated in %.1f s)'%(len(eqs),time.time()-t0),flush=True)
charts=[(1,1,1),(1,1,2),(1,2,1),(1,2,2),(1,2,3)]
tot=0; allunit=True
for (ja,jb,jc) in charts:
    par=[add(W('a%d'%ja),R2.const(-1)),add(W('b%d'%jb),R2.const(-1)),add(W('c%d'%jc),R2.const(-1))]
    if cal:
        norm=[add(W('r0'),R2.const(-1))]+[W('r%d'%j) for j in range(1,5)]
        u,n,s=RUN(eqs+fam+par+norm,names,p,'nc_cal'); tot+=s
        print('chart a%d=b%d=c%d=1, CALIBRATION rho = e_0: unit=%s basis size %s (%.1f s)'%(ja,jb,jc,u,n,s),flush=True)
        continue
    if e0:
        zero=['x%d0'%i for i in range(4)]+['x0%d'%ja,'x1%d'%jb,'x3%d'%jc]
        if e0cal:
            norm=[W(r) for r in rv]+[W(z) for z in zero[4:]]+[add(W('x00'),R2.const(-1))]
            u,n,s=RUN(eqs+fam+par+norm,names,p,'nce0c'); tot+=s
            print('chart a%d=b%d=c%d=1, E0-CALIBRATION (column 0 free, x00 = 1): unit=%s basis size %s (%.1f s)'%(ja,jb,jc,u,n,s),flush=True); continue
        for xn in [v for v in xv if v not in zero]:
            norm=[W(r) for r in rv]+[W(z) for z in zero]+[add(W(xn),R2.const(-1))]
            u,n,s=RUN(eqs+fam+par+norm,names,p,'nce0'); tot+=s; allunit=allunit and bool(u)
            if not u: print('chart a%d=b%d=c%d=1, %s=1: unit=%s basis size %s (%.1f s)'%(ja,jb,jc,xn,u,n,s),flush=True)
        print('chart a%d=b%d=c%d=1: 13 X-charts done, all unit so far: %s'%(ja,jb,jc,allunit),flush=True)
        continue
    for jr in range(1,5):
        norm=[W('r0'),sm(rv[1:]),add(W('r%d'%jr),R2.const(-1))]
        u,n,s=RUN(eqs+fam+par+norm,names,p,'nc'); tot+=s; allunit=allunit and bool(u)
        print('chart a%d=b%d=c%d=1, rho_%d=1: unit=%s basis size %s (%.1f s)'%(ja,jb,jc,jr,u,n,s),flush=True)
print('prime %d: total msolve time %.1f s; %s'%(p,tot,'calibration done' if cal else ('ALL CHARTS UNIT' if allunit else 'SOME CHART NOT UNIT')))
