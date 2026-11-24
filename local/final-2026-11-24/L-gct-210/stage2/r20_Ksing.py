# Kernel analysis with Singular doing the heavy algebra [NOTES-stage2 R20-1] (generalises r19_R1cof_sing.py to any cached F2col family, nq = 8).
# Prints: ranks (sympy over Q(params)), the common kernel k (constant?), q0(k,k); then Singular: det of the 7x7 principal minor (pivot index of k
# removed) of B_c with SYMBOLIC c, its c-coefficient ideal, saturated by EXC, minimal associated primes = the exact common rank-drop locus.
# usage: r20_Ksing.py CACHE "EXC polynomial"
import sys, pickle, subprocess, os, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; EXC=sys.argv[2] if len(sys.argv)>2 else '1'
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
print('fix',fix,'params',par,'nq',nq,'| detX',sp.factor(detX),'| dens',[sp.factor(d) for d in dens],'| rank-jump',rkjump,flush=True)
Bst=sp.Matrix.vstack(*Gs[1:]); rs=DM(Bst).rank(); print('rank q0',DM(Gs[0]).rank(),'| ranks B_z',[DM(G).rank() for G in Gs[1:]],'| B-stack',rs,flush=True)
if rs!=nq-1: print('common kernel dim',nq-rs,'-> not the standard case',flush=True); sys.exit(0)
k=DM(Bst).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
i=[j for j in range(nq) if k[j]!=0 and sp.sympify(k[j]).is_number][0]; k=k/k[i]
print('k =',list(k),'| q0(k,k) =',sp.factor(sp.cancel((k*Gs[0]*k.T)[0,0])),flush=True)
idx=[j for j in range(nq) if j!=i]
def smat(M): return ','.join(str(sp.expand(x)).replace('**','^') for x in M)
pv=','.join(map(str,par)); tag=os.path.basename(ck).replace('.pkl','')
L=['LIB "primdec.lib";','ring r=0,(c1,c2,c3,%s),dp;'%pv,'option(redSB);']
for z in (1,2,3): L.append('matrix B%d[7][7]=%s;'%(z,smat(Gs[z].extract(idx,idx))))
L+=['matrix B=c1*B1+c2*B2+c3*B3;','poly P=det(B);',
    'matrix Co=coeffs(coeffs(coeffs(P,c1),c2),c3);','ideal I=0; int k1; int k2;',
    'for(k1=1;k1<=nrows(Co);k1++){for(k2=1;k2<=ncols(Co);k2++){if(Co[k1,k2]!=0){I=I+Co[k1,k2];}}}',
    'ring s=0,(w,%s),dp;'%pv,'ideal I=imap(r,I);','ideal J=I+ideal(1-w*(%s));'%EXC.replace('**','^'),'J=eliminate(std(J),w);',
    'ring t=0,(%s),dp;'%pv,'ideal J=imap(s,J);','list Lp=minAssGTZ(J);','string S="";','for(int q=1;q<=size(Lp);q++){S=S+string(Lp[q])+"\\n";}',
    'if(size(Lp)==0){S="EMPTY (no common rank drop outside EXC)";}','write(":w /tmp/st2_ks_%s.out", S);'%tag,'quit;']
fn='/tmp/st2_ks_%s.sing'%tag; out='/tmp/st2_ks_%s.out'%tag
open(fn,'w').write('\n'.join(L)+'\n')
if os.path.exists(out): os.remove(out)
subprocess.run('ulimit -v '+os.environ.get('SMV','1500000')+'; timeout 3000 Singular -q %s > %s.err 2>&1'%(fn,fn),shell=True)
print('exact common rank-drop locus (minimal primes outside EXC):\n'+(open(out).read() if os.path.exists(out) else 'FAILED: '+open(fn+'.err').read()[-500:]),flush=True)
