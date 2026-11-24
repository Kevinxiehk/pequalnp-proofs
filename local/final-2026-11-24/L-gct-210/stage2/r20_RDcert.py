# CERTIFY a candidate common rank-drop locus over Q (or mod p for timing) [NOTES-stage2 R20-2]: I = c-coefficient ideal of det(c1 B1 + c2 B2 + c3 B3)
# restricted to the 7x7 principal minor (index of k removed). For each f in FS: test 1 in I + (1 - w*f*EXC) (Rabinowitsch, std over the field), i.e.
# f vanishes on V(I) outside V(EXC). All tests [1]  =>  V(I) \ V(EXC) is contained in V(FS)  (exact over Q in char 0).
# usage: r20_RDcert.py CACHE "EXC" "f1;f2;..." [CHAR]     env SING_ULIM (KB, default 1500000)
import sys, pickle, subprocess, os, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; EXC=sys.argv[2]; FS=[f for f in sys.argv[3].split(';') if f]; CH=sys.argv[4] if len(sys.argv)>4 else '0'
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
k=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
i=[j for j in range(nq) if k[j]!=0 and sp.sympify(k[j]).is_number][0]; idx=[j for j in range(nq) if j!=i]
def smat(M): return ','.join(str(sp.expand(x)).replace('**','^') for x in M)
pv=','.join(map(str,par)); tag=os.path.basename(ck).replace('.pkl','')+'_c'+CH
out='/tmp/st2_rdc_%s.out'%tag
L=['ring r=%s,(c1,c2,c3,%s),dp;'%(CH,pv),'option(redSB);']
for z in (1,2,3): L.append('matrix B%d[7][7]=%s;'%(z,smat(Gs[z].extract(idx,idx))))
L+=['matrix B=c1*B1+c2*B2+c3*B3;','poly P=det(B);','matrix Co=coeffs(coeffs(coeffs(P,c1),c2),c3);','ideal I=0; int k1; int k2;',
    'for(k1=1;k1<=nrows(Co);k1++){for(k2=1;k2<=ncols(Co);k2++){if(Co[k1,k2]!=0){I=I+Co[k1,k2];}}}',
    'ring s=%s,(w,%s),dp;'%(CH,pv),'ideal I=imap(r,I);','string S=""; ideal G;']
for f in FS:
    L+=['G=std(I+ideal(1-w*(%s)*(%s)));'%(f.replace('**','^'),EXC.replace('**','^')),'S=S+"%s: "+string(G[1]==1 and size(G)==1)+"\\n";'%f,'write(":w %s",S);'%out]
L+=['quit;']
fn='/tmp/st2_rdc_%s.sing'%tag; open(fn,'w').write('\n'.join(L)+'\n')
if os.path.exists(out): os.remove(out)
subprocess.run('ulimit -v %s; timeout %s Singular -q %s > %s.err 2>&1'%(os.environ.get('SING_ULIM','1500000'),os.environ.get('SING_TMO','3000'),fn,fn),shell=True)
print('fix',fix,'char',CH,'EXC',EXC,flush=True)
print(open(out).read() if os.path.exists(out) else 'FAILED: '+open(fn+'.err').read()[-400:],flush=True)
print('(1 = the Rabinowitsch ideal is the unit ideal: f vanishes on V(I) off V(EXC))',flush=True)
