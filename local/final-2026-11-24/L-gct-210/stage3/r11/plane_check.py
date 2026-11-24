# Round 11: does the common null cone K (exact, member TAG) contain a projective PLANE?  minAssGTZ over Q; every component of projective dim 2
# that is cut out by 4 linear forms and ONE quadric: rank of the quadric on the 4-dim linear space (exact). rank >= 3 => absolutely irreducible
# surface of degree 2 => no plane. A plane in K would lie in some 2-dim component; components of projective dim <= 1 cannot contain one.
import sys, subprocess, re, sympy as sp
TAG=sys.argv[1]; src=open('/home/kevxhk/work/L-gct-210/stage3/r11/ncdef_cone_exact_%s.sing'%TAG).read()
src=src.replace('ideal G=std(I);','LIB "primdec.lib";\nlist P=minAssGTZ(I);\nint i; for(i=1;i<=size(P);i++){ideal Q=std(P[i]); "COMP",i,dim(Q),mult(Q); "GENS"; Q; "END";}\nideal G=std(I);')
open('/tmp/pc_%s.sing'%TAG,'w').write(src)
out=subprocess.run(['/usr/bin/Singular','-q','/tmp/pc_%s.sing'%TAG],capture_output=True,text=True,timeout=600).stdout
xs=sp.symbols('x0:8'); comps=re.findall(r'COMP (\d+) (\d+) (\d+)\s*\nGENS\s*\n(.*?)\nEND',out,re.S)
ok=True
for idx,dim,deg,gens in comps:
    dim=int(dim); deg=int(deg)
    gl=[sp.sympify(g.split('=',1)[1].replace('^','**')) for g in gens.strip().split('\n') if '=' in g]
    if dim<3: print('component %s: projective dim %d, degree %d -> no plane'%(idx,dim-1,deg)); continue
    lin=[g for g in gl if sp.Poly(g,*xs).total_degree()==1]; quad=[g for g in gl if sp.Poly(g,*xs).total_degree()==2]
    # parametrise the linear space
    A=sp.Matrix([[sp.Poly(g,*xs).coeff_monomial(x) for x in xs] for g in lin]) if lin else sp.zeros(0,8)
    Nsp=A.nullspace() if lin else [sp.eye(8)[:,i] for i in range(8)]; us=sp.symbols('u0:%d'%len(Nsp)); free=list(us)
    sub={xs[i]:sum(Nsp[k][i]*us[k] for k in range(len(Nsp))) for i in range(8)}
    q=[sp.expand(g.subs(sub)) for g in quad]; q=[g for g in q if g!=0]
    if dim==3 and len(free)==4 and len(q)>=1:
        Hm=sp.hessian(q[0],free); r=Hm.rank()
        print('component %s: projective dim 2, degree %d, linear span dim %d, quadric rank %d -> %s'%(idx,deg,len(free),r,'NO plane' if r>=3 else 'MAY CONTAIN PLANES'))
        ok=ok and r>=3
    else:
        print('component %s: dim %d, linear span %d, %d quadrics -> inspect by hand'%(idx,dim,len(free),len(q))); ok=False
print('RESULT %s: K contains no projective plane: %s'%(TAG,ok))
