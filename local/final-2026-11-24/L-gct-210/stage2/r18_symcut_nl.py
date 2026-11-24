# Symmetry cut with NONLINEAR pieces, fiberwise in an extra parameter [NOTES-stage2 R18-3]. Coordinates (P0, a1, a2, a3), chart a4 = 1, where P0 is the
# ruling parameter (lam / nu), untouched by the group. S_3 permutes (a2, a3, a4) (polynomials are homogenised in (a1,a2,a3,a4), permuted, dehomogenised).
# A survivor with a2 a3 (a4 = 1) != 0 and outside EXC lies in INTERSECTION_sigma sigma^{-1}(union of PIECES). DFS over (sigma, piece) with pruning by
# Singular std over QQ (Rabinowitsch 1 - w * a2 * a3 * EXC); leaves -> minimal associated primes (minAssGTZ, char 0).
# usage: r18_symcut_nl.py PIECEFILE     (python file defining P0 (symbol name), PIECES = {name: [polys as strings]}, EXC = 'poly string')
import sys, os, itertools, subprocess, sympy as sp
spec={}; exec(open(sys.argv[1]).read(),spec)
P0=sp.Symbol(spec['P0']); a1,a2,a3,a4=sp.symbols('a1 a2 a3 a4'); V=[P0,a1,a2,a3]; loc={str(v):v for v in V}
PIECES={k:[sp.sympify(p,locals=loc) for p in v] for k,v in spec['PIECES'].items()}; EXC=sp.sympify(spec.get('EXC','1'),locals=loc)
perms=list(itertools.permutations([a2,a3,a4]))
def act(f,s):
    f=sp.expand(f); d=sp.Poly(f,a1,a2,a3).total_degree() if f.free_symbols&{a1,a2,a3} else 0
    F=sp.expand(a4**d*f.subs({a1:a1/a4,a2:a2/a4,a3:a3/a4},simultaneous=True)); F=sp.expand(sp.cancel(F))
    F=F.subs({a2:s[0],a3:s[1],a4:s[2]},simultaneous=True) if False else F.xreplace({a2:sp.Dummy('x2'),a3:sp.Dummy('x3'),a4:sp.Dummy('x4')})
    return F
def act2(f,s):
    f=sp.expand(f); d=max([sum(m[1:]) for m in sp.Poly(f,P0,a1,a2,a3).monoms()]) if f!=0 else 0
    F=sp.expand(sp.cancel(a4**d*f.subs({a1:a1/a4,a2:a2/a4,a3:a3/a4},simultaneous=True)))
    G=F.subs({a2:s[0],a3:s[1],a4:s[2]},simultaneous=True)
    return sp.expand(G.subs(a4,1))
wd='/tmp/st2_symnl_%d'%os.getpid(); os.makedirs(wd,exist_ok=True)
def singular(polys,final=False):
    out=wd+'/o.txt'; fn=wd+'/c.sing'
    if os.path.exists(out): os.remove(out)
    body='ring r=0,(w,%s),dp;\noption(redSB);\nideal I=%s,\n1-w*(%s);\n'%(','.join(map(str,V)),',\n'.join(str(p).replace('**','^') for p in polys),str(sp.expand(a2*a3*EXC)).replace('**','^'))
    if not final: body+='ideal G=std(I);\nif(G[1]==1){write(":w %s","EMPTY");}else{write(":w %s","NONEMPTY "+string(dim(G)));}\nquit;\n'%(out,out)
    else: body='LIB "primdec.lib";\n'+body+'ideal J=eliminate(I,w);\nring s=0,(%s),dp;\nideal J=imap(r,J);\nlist L=minAssGTZ(J);\nstring S="";\nfor(int i=1;i<=size(L);i++){S=S+string(L[i])+" | ";}\nwrite(":w %s",S);\nquit;\n'%(','.join(map(str,V)),out)
    open(fn,'w').write(body)
    subprocess.run('ulimit -v 2000000; timeout 600 Singular -q %s > /dev/null 2>&1'%fn,shell=True)
    return open(out).read().strip() if os.path.exists(out) else 'TIMEOUT'
acted={(k,i):[act2(p,s) for p in PIECES[k]] for k in PIECES for i,s in enumerate(perms)}
seen={}; leaves=set(); nodes=[0]
def dfs(i,polys,tag):
    key=(i,tuple(sorted(set(map(str,polys)))))
    if key in seen: return
    seen[key]=1; nodes[0]+=1
    if polys:
        r=singular(polys)
        if r.startswith('EMPTY'): return
        if r=='TIMEOUT': print('  TIMEOUT at',tag,flush=True)
    if i==len(perms): leaves.add(tuple(sorted(set(map(str,polys))))); print('  leaf',tag,flush=True); return
    for k in PIECES: dfs(i+1,polys+acted[(k,i)],tag+(k,))
dfs(0,[],())
print('nodes',nodes[0],'leaves',len(leaves),flush=True)
for L in leaves:
    print('LEAF',L,'\n   minimal primes:',singular([sp.sympify(p,locals=loc) for p in L],final=True)[:1500],flush=True)
