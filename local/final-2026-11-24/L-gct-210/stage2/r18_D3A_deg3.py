# D3A big-kernel degeneracy set with SINGULAR doing the heavy algebra [NOTES-stage2 R19-2] (the sympy versions were too slow).
# Exports: B_c[Q,Q] for 3 random c (Q = complement of the rref pivots of K), the polynomial rref basis of K, q0; Singular computes det B_c[Q,Q],
# the gcd / common zeros, the K-basis degeneration (rref denominators), det q0|K.
import pickle, random, subprocess, os, sympy as sp
from sympy.polys.matrices import DomainMatrix
_,_,_,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r18/cache_D3A.pkl','rb'))
F=sp.QQ.frac_field(*par); q0=Gs[0]; Bs=Gs[1:]
K=DomainMatrix.from_Matrix(sp.Matrix.vstack(*Bs)).convert_to(F).nullspace().to_Matrix()
Rr,piv=DomainMatrix.from_Matrix(K).convert_to(F).rref(); Kr=Rr.to_Matrix().applyfunc(sp.cancel)
den=sp.lcm([sp.fraction(sp.together(x))[1] for x in Kr]); Kp=(Kr*den).applyfunc(lambda x: sp.expand(sp.cancel(x)))
Q=[j for j in range(nq) if j not in piv]
print('pivots',piv,'complement',Q,'rref denominators',sp.factor(den),flush=True)
def smat(M): return ','.join(str(sp.expand(x)).replace('**','^') for x in M)
lines=['ring r=0,(a2,a3),dp;','option(redSB);']
for t,seed in enumerate((2,7,11)):
    random.seed(seed); c=[random.randint(1,9) for _ in Bs]; B=sum((ci*M for ci,M in zip(c,Bs)),sp.zeros(nq,nq)).extract(Q,Q)
    lines.append('matrix B%d[5][5]=%s;'%(t,smat(B))); lines.append('poly d%d=det(B%d);'%(t,t))
lines.append('matrix Kp[3][%d]=%s;'%(nq,smat(Kp))); lines.append('matrix G0[%d][%d]=%s;'%(nq,nq,smat(q0)))
lines.append('poly dq=det(Kp*G0*transpose(Kp));')
lines.append('poly g=gcd(d0,gcd(d1,d2));')
lines.append('ideal Rz=std(ideal(d0/g,d1/g,d2/g));')
lines.append('write(":w /tmp/st2_d3a_deg3.out", "gcd of det B_c[Q,Q]: "+string(factorize(g))+"\\nresidual common zeros (std): "+string(Rz)+"\\ndet q0|K: "+string(factorize(dq)));')
lines.append('quit;')
open('/tmp/st2_d3a_deg3.sing','w').write('\n'.join(lines)+'\n')
if os.path.exists('/tmp/st2_d3a_deg3.out'): os.remove('/tmp/st2_d3a_deg3.out')
subprocess.run('ulimit -v 1500000; timeout 1800 Singular -q /tmp/st2_d3a_deg3.sing > /tmp/st2_d3a_deg3.err 2>&1',shell=True)
print(open('/tmp/st2_d3a_deg3.out').read() if os.path.exists('/tmp/st2_d3a_deg3.out') else 'SINGULAR FAILED: '+open('/tmp/st2_d3a_deg3.err').read()[-500:],flush=True)
print('setup-exceptional: detX',sp.factor(detX),'| den',[sp.factor(x) for x in dens],'| rank-jump',rkjump,flush=True)
