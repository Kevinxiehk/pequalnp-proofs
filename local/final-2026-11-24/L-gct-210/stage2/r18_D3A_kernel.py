# Kernel analysis for D003-PROP Case A (forms of r14_D3A_fx.py) [NOTES-stage2 R18-2]: q0 = the z^0 coefficient form, B-forms = all other coefficient forms.
import sys, pickle, random, itertools, sympy as sp
sys.argv=['r14_D3A_fx.py','0']
src=open('/home/kevxhk/work/L-gct-210/stage2/r14_D3A_fx.py').read().split("ys=[[sp.Symbol('y%d_%d'%(r,c))")[0]
exec(src)
from sympy.polys.matrices import DomainMatrix
Fd=sp.QQ.frac_field(*par); DMf=lambda M: DomainMatrix.from_Matrix(M).convert_to(Fd)
mons=sorted(monos); i0=mons.index((0,0,0,0,0)); q0=mats[i0]; Bs_=[M for k,M in enumerate(mats) if k!=i0]
print('nq',nq,'forms',len(mats),'| rank q0',DMf(q0).rank(),'| ranks of B-forms',[DMf(M).rank() for M in Bs_],flush=True)
St=sp.Matrix.vstack(*Bs_); rs=DMf(St).rank(); print('rank of B-stack',rs,'-> common kernel dim',nq-rs,flush=True)
random.seed(2); Bc=sum((random.randint(1,9)*M for M in Bs_),sp.zeros(nq,nq)); rc=DMf(Bc).rank(); print('generic B_c rank',rc,flush=True)
if nq-rs>0:
    K=DMf(St).nullspace().to_Matrix().applyfunc(sp.cancel); print('common kernel K:',K.tolist(),flush=True)
    print('q0 on K:',(K*q0*K.T).applyfunc(sp.factor).tolist(),flush=True)
m=4-rc//2; print('L\'\' meets ker B_c in dim >=',m,'; ker B_c = K:',nq-rc==nq-rs,flush=True)
pickle.dump((None,None,None,a2s,a3s,par,[q0]+Bs_,co,nq,[den],detX,rkjump,fix),open('/home/kevxhk/work/L-gct-210/stage2/r18/cache_D3A.pkl','wb'))
print('saved r18/cache_D3A.pkl',flush=True)
