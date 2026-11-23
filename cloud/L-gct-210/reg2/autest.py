# Test: for every row i with single-row part e_i (x) U_i in M:  Omega(M) inside A(U_i) := {s : U_i o s inside U_i + C1} ?
# and the column analogue: single-column part K_c (x) e_c:  every s in Omega(M) ... (report only rows here).
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed
from a5 import onb, rref_tol
from a6 import T1
rg=np.random.default_rng(0)
def AU(U):
    # s with (w o s) in U + C1 for all w in U: linear conditions <a, w o s> = 0 for a in (U + C1)^perp
    A=np.concatenate([U,np.ones((1,5))],0); ann=null(A)       # rows a with A a = 0 (bilinear)
    conds=[a*w for a in ann for w in U]                         # <a o w, s> = 0
    if not conds: return np.eye(5,dtype=complex)
    return null(np.array(conds))
def inside(V,W,tol=1e-6):
    # is span(V) inside span(W) (row spaces)?
    if len(V)==0: return True
    return rank(np.concatenate([W,V],0),tol)==rank(W,tol)
files=sorted(glob.glob('Mstar2.npy')+glob.glob('ec_*.npy')[:6]+glob.glob('ec2_*.npy')[:6]+glob.glob('dr_u3_s1_1.npy')+glob.glob('linespan_other_s2_*.npy')+glob.glob('M_L080_col0.npy')+glob.glob('M_ex2_row4.npy')+glob.glob('../rows/rc45.npy'))
lims=['nc_d6_k1_s23','nc_d6_k1_s4','seed_d6_e3_t4','nc_d6_k1_s21','nc_d6_k1_s20','nc_d6_k1_s17','clm_p4_d6_defect3_s12','seed_d6_e3_t3']
spaces=[(f,onb(np.load(f))) for f in files]+[(f,onb(rref_tol(onb(np.load('../rows/%s.npy'%f)),1e-5))) for f in lims]
viol=0; tot=0; eq=0
for f,B in spaces:
    T=T1(embed(B),rg,npts=130); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-7*S[0]).sum()); Om=U_[:,:r].T
    out=[]
    for i in range(4):
        SR=rowpart(B,[i])
        if len(SR)==0: continue
        A=AU(SR[:,i,:]); ok=inside(Om,A); tot+=1; viol+= (not ok); eq+= (ok and len(A)==r)
        out.append('row %d: u=%d dim A(U)=%d %s'%(i,len(SR),len(A),'OK' if ok else 'VIOLATED'))
    print('%-34s dim Omega %d | %s'%(f.split('/')[-1],r,' ; '.join(out)))
print('rows tested %d, violations %d, equalities Omega = A(U_i): %d'%(tot,viol,eq))
