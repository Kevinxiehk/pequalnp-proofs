# Round 14: deformations of 3-DIM single-line parts by skew maps (never scanned before; NOTES-reg2 22.2).  For a part V = <v1,v2,v3> (three
# generically independent spanning elements kept, the rest zeroed) with Gram G, B = adj(G) S, S = [[0,s3,-s2],[-s3,0,s1],[s2,-s1,0]] (skew,
# rank 2, kernel adj(G)^{-1}-dual of s): v_k -> v_k + e_tgt (B v_k) placed in the target row (column).  Components of the level ideal in
# (base params, s1, s2, s3) that are NOT inside {s = 0} are printed.  usage: defo_scan3.py FAMILY
import sys, subprocess, os, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import numpy as np, random
from famtool import *
fam=sys.argv[1]; src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
R0=Ring(P0); Bs0=bfn(R0,R0.var); pt=[complex(random.gauss(0,1),random.gauss(0,1)) for _ in P0]
def ev(q): return sum(complex(v)*np.prod([x**e for e,x in zip(k,pt)]) for k,v in q.items()) if q else 0
groups=[]
for kind in ('col','row'):
    for idx in range(5 if kind=='col' else 4):
        g=[k for k,B in enumerate(Bs0) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
        if len(g)<3: continue
        vecs=np.array([[ev(Bs0[k][i][idx]) for i in range(4)] if kind=='col' else [ev(Bs0[k][idx][j]) for j in range(5)] for k in g])
        if np.linalg.matrix_rank(vecs,tol=1e-8)!=3: continue
        trip=next(t for t in itertools.combinations(range(len(g)),3) if np.linalg.matrix_rank(vecs[list(t)],tol=1e-8)==3)
        groups.append((kind,idx,[g[t] for t in trip],[k for k in g if k not in [g[t] for t in trip]]))
print('family %s: 3-dim single-line parts (kept, dropped): %s'%(fam,[(k,i,kp,dr) for k,i,kp,dr in groups]),flush=True)
def dot(R,a,b):
    t={}
    for x,y in zip(a,b):
        if x and y: t=add(t,mul(x,y))
    return t
for (kind,idx,keep,drop) in groups:
    for tgt in range(5 if kind=='col' else 4):
        if tgt==idx: continue
        PP=P0+['s1','s2','s3']
        def bf(R,V):
            Bs=bfn(R,V)
            for k in drop: Bs[k]=[[{} for _ in range(5)] for _ in range(4)]
            v=[[Bs[g][i][idx] for i in range(4)] if kind=='col' else [Bs[g][idx][j] for j in range(5)] for g in keep]
            G=[[dot(R,v[a],v[b]) for b in range(3)] for a in range(3)]
            def det2(a,b,c,d_): return add(mul(a,d_) if a and d_ else {},mul(b,c) if b and c else {},-1)
            adj=[[None]*3 for _ in range(3)]
            for a in range(3):
                for b in range(3):
                    rr=[x for x in range(3) if x!=b]; cc=[x for x in range(3) if x!=a]
                    m=det2(G[rr[0]][cc[0]],G[rr[0]][cc[1]],G[rr[1]][cc[0]],G[rr[1]][cc[1]])
                    adj[a][b]=m if (a+b)%2==0 else scal(m,-1)
            s1,s2,s3=V('s1'),V('s2'),V('s3'); S=[[{},s3,scal(s2,-1)],[scal(s3,-1),{},s1],[s2,scal(s1,-1),{}]]
            Bm=[[{} for _ in range(3)] for _ in range(3)]
            for a in range(3):
                for b in range(3):
                    for c_ in range(3):
                        if adj[a][c_] and S[c_][b]: Bm[a][b]=add(Bm[a][b],mul(adj[a][c_],S[c_][b]))
            for b in range(3):          # B v_b = sum_a Bm[a][b] v_a
                img=[{} for _ in range(len(v[0]))]
                for a in range(3):
                    if Bm[a][b]:
                        for k in range(len(v[0])):
                            if v[a][k]: img[k]=add(img[k],mul(Bm[a][b],v[a][k]))
                g=keep[b]
                for k in range(len(v[0])):
                    if img[k]:
                        if kind=='col': Bs[g][k][tgt]=add(Bs[g][k][tgt],img[k]) if Bs[g][k][tgt] else img[k]
                        else: Bs[g][tgt][k]=add(Bs[g][tgt][k],img[k]) if Bs[g][tgt][k] else img[k]
            return Bs
        F=Family(PP,bf,d)
        lv=[to_str_Q({k[:len(PP)]:v for k,v in q.items()},PP) for q in F.level]
        if not lv: print('  %s %d -> %d: LEVEL FOR ALL (params, s)'%(kind,idx,tgt),flush=True); continue
        sc='LIB "primdec.lib";\nring R=0,(%s),dp;\nideal I=%s;\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){ideal J=std(L[i]); if(reduce(s1,J)!=0 or reduce(s2,J)!=0 or reduce(s3,J)!=0){print("COMP");print(L[i]);} kill J;}\nquit;\n'%(','.join(PP),','.join('('+l+')' for l in lv))
        fn='/tmp/defo3_%s_%d.sing'%(fam,os.getpid()); open(fn,'w').write(sc)
        try: r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=600)
        except subprocess.TimeoutExpired: print('  %s %d -> %d: TIMEOUT'%(kind,idx,tgt),flush=True); continue
        out=r.stdout; out='\n'.join(l for l in out.split('\n') if not l.startswith('// **'))
        comps=[' '.join(c.split()) for c in out.split('COMP')[1:]]
        print('  %s %d -> %d: genuine loci (s not 0): %s'%(kind,idx,tgt,comps if comps else 'NONE'),flush=True)
