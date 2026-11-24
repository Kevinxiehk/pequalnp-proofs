# verify2 r12: does (alpha1) with |supp W| = 3 die in degree 2 (like (alpha0))?  M = v (x) Psi + sig*ka g (x) f + n3 (x) psi3 + u3 (x) f,
# v = chi_1 (special, forced for supp 3), g = chi_2/2 (unit, perp v), <u3,u3> = ka^2, <u3,n3> = 0, n3 isotropic; condition
# 4 + 3(M + M^T) + M^T M + 4 ka^2 f f^T = 0 on V (from A_4 = -3 - M, A_4^*A_4 = 5 - 4 k f f^T); ka != 0, f != 0 (charts f_i = 1).
import sympy as sp, itertools, subprocess
I=sp.I
chi=[[I**(k*r) for r in range(4)] for k in range(4)]
P=sp.symbols('P0:3'); Q=sp.symbols('Q0:3'); Fv=sp.symbols('F0:3'); U=sp.symbols('U0:3'); s=sp.symbols('s0:3'); ka,t3,zz=sp.symbols('ka t3 zz')
vecV=lambda c:[c[0],c[1],c[2],-c[0]-c[1]-c[2]]
dot=lambda a,b: sp.expand(sum(x*y for x,y in zip(a,b)))
v=chi[1]; g=[x/2 for x in chi[2]]
w=lambda t:[chi[1][r]+2*t*chi[2][r]-2*t**2*chi[3][r] for r in range(4)]
out=[]
for sig in (1,-1,3,-3):
  for n3name,n3,nv in (('w(t3)',w(t3),'t3'),('chi3',chi[3],'')):
    for fc in range(3):
        Psi=vecV(P); psi3=vecV(Q); f=vecV(Fv); u3=vecV(U); S=vecV(s)
        Ms=[v[r]*dot(Psi,S)+sig*ka*g[r]*dot(f,S)+n3[r]*dot(psi3,S)+u3[r]*dot(f,S) for r in range(4)]
        MTs=[Psi[r]*dot(v,S)+sig*ka*f[r]*dot(g,S)+psi3[r]*dot(n3,S)+f[r]*dot(u3,S) for r in range(4)]
        Qf=sp.expand(4*dot(S,S)+3*(dot(S,Ms)+dot(S,MTs))+dot(Ms,Ms)+4*ka**2*dot(f,S)**2)
        eqs=list(sp.Poly(Qf,*s).coeffs())+[dot(u3,u3)-ka**2,dot(u3,n3),zz*ka-1,Fv[fc]-1]
        vars_='P0,P1,P2,Q0,Q1,Q2,F0,F1,F2,U0,U1,U2,ka,zz'+(','+nv if nv else '')
        sc='ring R=(0,I),(%s),dp; minpoly=I^2+1; option(redSB);\nideal E=%s;\nideal G=std(E); printf("sig=%d n3=%s f%d=1: unit %%s dim %%s",reduce(1,G)==0,dim(G)); quit;\n'%(vars_,','.join(str(sp.expand(e)).replace('**','^') for e in eqs),sig,n3name,fc)
        open('a1s3_deg2.sing','w').write(sc)
        r=subprocess.run(['Singular','-q','a1s3_deg2.sing'],capture_output=True,text=True,timeout=600).stdout.strip()
        print(r,flush=True)
