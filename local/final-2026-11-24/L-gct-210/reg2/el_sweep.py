import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
import el_test as E
from a5 import onb
from t import *
rg=E.rg
def sweep(name,B,i,dims=(2,),trials=4):
    Mi=rowpart(B,[k for k in range(4) if k!=i]); res=[]
    for d in dims:
        if d>len(Mi): continue
        for _ in range(trials):
            C=rg.normal(size=(d,len(Mi)))+1j*rg.normal(size=(d,len(Mi))); S=onb(np.einsum('kc,cab->kab',C,Mi))
            MS,U=E.saturate(S,i); Om,nT=E.omega(MS); A=E.AU(U) if len(U) else np.eye(5,dtype=complex)
            res.append((d,len(MS),len(Om),len(A),E.inside(Om,A)))
    bad=[r for r in res if not r[4]]
    print('%-28s dim M_i %d: %d tests, %d violations; (dimS,dimM_S,dimOm,dimA) samples %s'%(name,len(Mi),len(res),len(bad),sorted(set(r[:4] for r in res))[:6]),flush=True)
from dr211b_num import fam as fam2, member_g, cross4
from dr22_num_lib import fam22
from p312_lib import fam as fam312
from dr211iii_num_lib import fam as fam3
for k in range(2):
    a,b,c=member_g(rg); sweep('(2,1,1|2)(ii) gen %d'%k,onb(fam2(a,b,c)),0,dims=(2,3))
b=np.array([1,-1,0,0],complex); c=np.array([0,0,1,-1],complex); sweep('(2,1,1|2)(ii) D',onb(fam2(cross4(b,c),b,c)),0,dims=(2,3))
sweep('(2,1,1|2)(iii) gen',onb(fam3(0.3+0.1j,-0.7)),1,dims=(2,3))
sweep('(2,2|2) mu=(0,1,0,1)',onb(fam22(0,1)),1,dims=(2,3))
sweep('(3,1|2) m=(1,w,w2,0,0)',onb(fam312(np.array([1,np.exp(2j*np.pi/3),np.exp(4j*np.pi/3),0,0]))),0,dims=(2,3))
sweep('(3,1|2) generic',onb(fam312(np.array([1,2,-0.5,-2.5,0]))),0,dims=(2,3))
sweep('Mstar2',onb(np.load('/home/kevxhk/work/L-gct-210/reg2/Mstar2.npy')),3,dims=(2,3))
sweep('M_L080_col0 (F)',onb(np.load('/home/kevxhk/work/L-gct-210/reg2/M_L080_col0.npy')),0,dims=(2,))
