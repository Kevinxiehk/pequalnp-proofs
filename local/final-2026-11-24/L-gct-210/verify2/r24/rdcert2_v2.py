# Lighter exact RD certificate using the FACTORED structure of P(c) = det(c1 B1 + c2 B2 + c3 B3)[7x7] [NOTES-stage2 R21-3].
# Singular: P (symbolic c); divide by a given polynomial factor DIV (exactness checked: remainder 0); the c-coefficients of the quotient Q generate J_Q;
# then for f in FS test 1 in J_Q + (1 - w f EXC) over QQ. Since P = DIV * Q, {P(c) = 0 for all c} = V(DIV-part: all c-coefficients of DIV) u V(J_Q);
# the DIV part is handled by hand (e.g. c.a == 0 for all c <=> a = 0).
# usage: r21_RDcert2.py CACHE "DIV" "EXC" "f1;f2"   env SING_ULIM
import sys, pickle, subprocess, os, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; DIV=sys.argv[2]; EXC=sys.argv[3]; FS=[f for f in sys.argv[4].split(';') if f]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
k=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
i=[j for j in range(nq) if k[j]!=0 and sp.sympify(k[j]).is_number][0]; idx=[j for j in range(nq) if j!=i]
def smat(M): return ','.join(str(sp.expand(x)).replace('**','^') for x in M)
pv=','.join(map(str,par)); tag=os.path.basename(ck).replace('.pkl',''); out='/tmp/v2_rdc2_%s.out'%tag
L=['ring r=0,(c1,c2,c3,%s),dp;'%pv,'option(redSB);']
for z in (1,2,3): L.append('matrix B%d[7][7]=%s;'%(z,smat(Gs[z].extract(idx,idx))))
L+=['matrix B=c1*B1+c2*B2+c3*B3;','poly P=det(B);','poly D=%s;'%DIV.replace('**','^'),
    'list qr=division(P,D);','poly Q=qr[1][1,1]; poly Rm=qr[2][1];',
    'string S="remainder zero: "+string(Rm==0)+" | unit factor: "+string(qr[3][1,1])+"\\n";','write(":w %s",S);'%out,
    'matrix Co=coeffs(coeffs(coeffs(Q,c1),c2),c3);','ideal I=0; int k1; int k2;',
    'for(k1=1;k1<=nrows(Co);k1++){for(k2=1;k2<=ncols(Co);k2++){if(Co[k1,k2]!=0){I=I+Co[k1,k2];}}}',
    'S=S+"J_Q generators: "+string(size(I))+", max degree "+string(deg(I))+"\\n";','write(":w %s",S);'%out,
    'ring s=0,(w,%s),dp;'%pv,'ideal I=imap(r,I);','ideal G;']
for f in FS:
    L+=['G=std(I+ideal(1-w*(%s)*(%s)));'%(f.replace('**','^'),EXC.replace('**','^')),'S=S+"%s: "+string(G[1]==1 and size(G)==1)+"\\n";'%f,'write(":w %s",S);'%out]
L+=['quit;']
fn='/tmp/v2_rdc2_%s.sing'%tag; open(fn,'w').write('\n'.join(L)+'\n')
if os.path.exists(out): os.remove(out)
subprocess.run('ulimit -v %s; timeout %s Singular -q %s > %s.err 2>&1'%(os.environ.get('SING_ULIM','1500000'),os.environ.get('SING_TMO','3000'),fn,fn),shell=True)
print('fix',fix,'| DIV',DIV,'| EXC',EXC,flush=True)
print(open(out).read() if os.path.exists(out) else 'FAILED: '+open(fn+'.err').read()[-400:],flush=True)
