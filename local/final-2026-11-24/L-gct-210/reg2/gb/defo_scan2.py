# SECOND skew-deformation scan (round 8): start from FAMILY with a first deformation (kind,idx,tgt; parameter t) restricted to an optional
# locus (relations "r1;r2"), then try every remaining 2-element single-line group with a second deformation (parameter t2).  Reports the
# components of the level ideal on which NEITHER t nor t2 is forced to 0.   usage: defo_scan2.py FAMILY kind,idx,tgt ["rel1;rel2"]
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
fam,d1=sys.argv[1],sys.argv[2]; locus=[x for x in (sys.argv[3].split(';') if len(sys.argv)>3 else []) if x]
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); cut=src.index('F=Family(params,bfn,d)')
sys.argv=['x',fam,'16','1','1']; exec(src[:cut])
base_bfn=bfn; P0=list(params)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def dotv(a,b):
    t={}
    for x,y in zip(a,b):
        if x and y: t=add(t,mul(x,y))
    return t
def deform(Bs,grp,kind,idx,tgt,t):
    v=[[Bs[g][i][idx] for i in range(4)] if kind=='col' else [Bs[g][idx][j] for j in range(5)] for g in grp]
    g11=dotv(v[0],v[0]); g12=dotv(v[0],v[1]); g22=dotv(v[1],v[1])
    Jv=[[add(mul(g12,v[0][k]) if v[0][k] else {}, mul(g11,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))],
        [add(mul(g22,v[0][k]) if v[0][k] else {}, mul(g12,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))]]
    for n,g in enumerate(grp):
        for k in range(len(v[0])):
            if Jv[n][k]:
                if kind=='col': Bs[g][k][tgt]=add(Bs[g][k][tgt],mul(t,Jv[n][k])) if Bs[g][k][tgt] else mul(t,Jv[n][k])
                else: Bs[g][tgt][k]=add(Bs[g][tgt][k],mul(t,Jv[n][k])) if Bs[g][tgt][k] else mul(t,Jv[n][k])
def groups_of(Bs):
    out=[]
    for kind in ('col','row'):
        for idx in range(5 if kind=='col' else 4):
            g=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
            if len(g)==2: out.append((kind,g,idx))
    return out
k1,i1,t1=d1.split(','); i1=int(i1); t1=int(t1)
R0=Ring(['y%d'%k for k in range(1,d+1)]+P0+['t','t2']); B0=base_bfn(R0,R0.var)
g1=[g for (kk,g,ii) in groups_of(B0) if kk==k1 and ii==i1][0]
deform(B0,g1,k1,i1,t1,R0.var('t'))
rest=[(kk,g,ii) for (kk,g,ii) in groups_of(B0)]
print('family %s with first deformation %s (locus %s); remaining 2-element groups: %s'%(fam,d1,locus,[(kk,ii) for kk,g,ii in rest]),flush=True)
for (k2,g2,i2) in rest:
    for tg in range(5 if k2=='col' else 4):
        if tg==i2: continue
        def bf(R,V):
            Bs=base_bfn(R,V); deform(Bs,g1,k1,i1,t1,V('t')); deform(Bs,g2,k2,i2,tg,V('t2')); return Bs
        F=Family(P0+['t','t2'],bf,d)
        lv=[to_str_Q({k[:len(P0)+2]:v for k,v in q.items()},P0+['t','t2']) for q in F.level]
        if not lv: print('  second %s %d -> %d: LEVEL FOR ALL'%(k2,i2,tg),flush=True); continue
        sc='LIB "primdec.lib";\nring R=0,(%s),dp;\nideal I=%s;\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}\nquit;\n'%(','.join(P0+['t','t2']),','.join(['('+l+')' for l in lv]+['('+x+')' for x in locus]))
        open('/tmp/ds2_%s.sing'%fam,'w').write(sc)
        r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/ds2_%s.sing'%fam),capture_output=True,text=True,timeout=900)
        comps=[' '.join(c.split()) for c in r.stdout.split('COMP')[1:]]
        live=[c for c in comps if not any(g.strip() in ('t','t2') for g in c.split(','))]
        print('  second %s %d -> %d: %s'%(k2,i2,tg,live if live else 'NONE'),flush=True)
