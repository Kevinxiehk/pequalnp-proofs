# Systematic SKEW-DEFORMATION scan of the exact line-spanned families (NOTES-reg2 15.4).  For a family of gen_rank.py (FAMS) and every pair of
# basis elements supported in the same single column a (resp. single row i), and every other column b (resp. row j): replace the pair (v1, v2)
# by v_k + t * J(v_k) placed in column b (resp. row j), J = adj(G) S on span(v1, v2) (G = Gram matrix, S = [[0,1],[-1,0]]; polynomial, skew).
# The level equations of the deformed family (params + t) are decomposed (Singular minAssGTZ); components on which t is NOT forced to 0
# are deformation loci.   usage: defo_scan.py FAMILY
import sys, subprocess, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read()
fam=sys.argv[1]; sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]
    return set(i for i,j in cells), set(j for i,j in cells)
def dotv(R,a,b):
    t={}
    for x,y in zip(a,b):
        if x and y: t=add(t,mul(x,y))
    return t
def run(kind,grp,tgt):
    def bf(R,V):
        Bs=bfn(R,V); t=V('t')
        v=[ [Bs[g][i][grp[2]] if kind=='col' else None for i in range(4)] if kind=='col' else [Bs[g][grp[2]][j] for j in range(5)] for g in grp[:2]]
        g11=dotv(R,v[0],v[0]); g12=dotv(R,v[0],v[1]); g22=dotv(R,v[1],v[1])
        Jv=[[add(mul(g12,v[0][k]) if v[0][k] else {}, mul(g11,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))],
            [add(mul(g22,v[0][k]) if v[0][k] else {}, mul(g12,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))]]
        for n,g in enumerate(grp[:2]):
            for k in range(len(v[0])):
                if Jv[n][k]:
                    if kind=='col': Bs[g][k][tgt]=add(Bs[g][k][tgt],mul(t,Jv[n][k])) if Bs[g][k][tgt] else mul(t,Jv[n][k])
                    else: Bs[g][tgt][k]=add(Bs[g][tgt][k],mul(t,Jv[n][k])) if Bs[g][tgt][k] else mul(t,Jv[n][k])
        return Bs
    F=Family(P0+['t'],bf,d)
    lv=[to_str_Q({k[:len(P0)+1]:v for k,v in q.items()},P0+['t']) for q in F.level]
    if not lv: return 'LEVEL FOR ALL (params, t)'
    sc='LIB "primdec.lib";\nring R=0,(%s),dp;\nideal I=%s;\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}\nquit;\n'%(','.join(P0+['t']),','.join('('+l+')' for l in lv))
    open('/tmp/defo_%s.sing'%fam,'w').write(sc)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/defo_%s.sing'%fam),capture_output=True,text=True,timeout=900)
    comps=[' '.join(c.split()) for c in r.stdout.split('COMP')[1:]]
    live=[c for c in comps if not any(g.strip()=='t' for g in c.split(','))]
    return 'deformation loci (t not forced to 0): %s'%(live if live else 'NONE')
R0=Ring(['y%d'%k for k in range(1,d+1)]+P0+['x%d%d'%(i,j) for i in range(4) for j in range(5)]+['r%d'%j for j in range(5)]+['t'])
Bs0=bfn(R0,R0.var)
groups=[]
for kind in ('col','row'):
    for idx in range(5 if kind=='col' else 4):
        g=[k for k,B in enumerate(Bs0) if support(B)==((support(B)[0],{idx}) if kind=='col' else ({idx},support(B)[1])) and len(support(B)[1 if kind=='col' else 0])==1]
        if len(g)==2: groups.append((kind,g[0],g[1],idx))
print('family %s: 2-element single-line groups: %s'%(fam,[(k,a,b,i) for (k,a,b,i) in groups]),flush=True)
for (kind,a,b,idx) in groups:
    for tgt in range(5 if kind=='col' else 4):
        if tgt==idx: continue
        print('  %s %d -> %d: %s'%(kind,idx,tgt,run(kind,(a,b,idx),tgt)),flush=True)
