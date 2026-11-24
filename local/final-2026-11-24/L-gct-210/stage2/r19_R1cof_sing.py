# EXACT common rank-drop locus of R1 by Singular [NOTES-stage2 R19-4]: det of the 7x7 principal minor (index i = 6 removed, k = e7 - e6 normalised at 6)
# of B_c = c1 B1 + c2 B2 + c3 B3 with c SYMBOLIC; its c-coefficients generate the ideal of {rank B_c < 7 for all c}; saturate by lam*a1*D and take
# minimal associated primes over QQ.
import pickle, subprocess, os, sympy as sp
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r14/cache_F2col_05c7df28474c.pkl','rb'))
i=6; idx=[j for j in range(nq) if j!=i]
def smat(M): return ','.join(str(sp.expand(x)).replace('**','^') for x in M)
L=['LIB "primdec.lib";','ring r=0,(c1,c2,c3,lam,a1,a2,a3),dp;','option(redSB);']
for z in (1,2,3): L.append('matrix B%d[7][7]=%s;'%(z,smat(Gs[z].extract(idx,idx))))
L+=['matrix B=c1*B1+c2*B2+c3*B3;','poly P=det(B);','write(":w /tmp/st2_r1cof.P", string(size(P))+" terms, deg "+string(deg(P)));',
    'matrix Co=coeffs(coeffs(coeffs(P,c1),c2),c3);',
    'ideal I=0; int k1; int k2;',
    'for(k1=1;k1<=nrows(Co);k1++){for(k2=1;k2<=ncols(Co);k2++){if(Co[k1,k2]!=0){I=I+Co[k1,k2];}}}',
    'ring s=0,(w,lam,a1,a2,a3),dp;','ideal I=imap(r,I);','ideal J=I+ideal(1-w*lam*a1*(a1+a2+a3-4));','J=eliminate(std(J),w);',
    'ring t=0,(lam,a1,a2,a3),dp;','ideal J=imap(s,J);','list Lp=minAssGTZ(J);','string S="";','for(int q=1;q<=size(Lp);q++){S=S+string(Lp[q])+"\\n";}',
    'write(":w /tmp/st2_r1cof.out", S);','quit;']
open('/tmp/st2_r1cof.sing','w').write('\n'.join(L)+'\n')
for f in ('/tmp/st2_r1cof.out','/tmp/st2_r1cof.P'):
    if os.path.exists(f): os.remove(f)
subprocess.run('ulimit -v 1500000; timeout 3000 Singular -q /tmp/st2_r1cof.sing > /tmp/st2_r1cof.err 2>&1',shell=True)
print('P:',open('/tmp/st2_r1cof.P').read() if os.path.exists('/tmp/st2_r1cof.P') else 'none')
print('minimal primes of the common rank-drop locus (outside lam*a1*D):\n'+(open('/tmp/st2_r1cof.out').read() if os.path.exists('/tmp/st2_r1cof.out') else 'FAILED: '+open('/tmp/st2_r1cof.err').read()[-600:]))
