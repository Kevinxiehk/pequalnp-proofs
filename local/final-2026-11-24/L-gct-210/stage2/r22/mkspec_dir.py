# build a r22_genset spec from a Dir_*.sing U-matrix (X basis = z_k coefficients of U - J), with parameter substitutions
import sys, re
src=sys.argv[1]; subs=sys.argv[2]; out=sys.argv[3]
lines=[l for l in open(src) if l.startswith('U[')]
ent={}
for l in lines:
    m=re.match(r'U\[(\d),(\d)\]=(.*);',l.strip()); i,j,e=int(m.group(1))-1,int(m.group(2))-1,m.group(3); ent[(i,j)]=e
S=['import sympy as sp','r1,r2,f0,f3,sg,d0,d3,z1,z2,z3,z4,z5=sp.symbols("r1 r2 f0 f3 sg d0 d3 z1 z2 z3 z4 z5")','SUBS={%s}'%subs,'PAR=[]','BS=[]',
   'E={%s}'%','.join('(%d,%d):"%s"'%(i,j,e) for (i,j),e in ent.items()),
   'for k,z in enumerate([z1,z2,z3,z4,z5]):',
   '    M=sp.zeros(5,5)',
   '    for (i,j),e in E.items():',
   '        ex=sp.sympify(e.replace("^","**"),locals=dict(r1=r1,r2=r2,f0=f0,f3=f3,sg=sg,d0=d0,d3=d3,z1=z1,z2=z2,z3=z3,z4=z4,z5=z5))',
   '        M[i,j]=sp.expand(sp.diff(ex,z).subs(SUBS))',
   '    BS.append(M)']
open(out,'w').write('\n'.join(S)+'\n'); print('spec written',out)
