import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, glob
from ext6 import *
from r5_FO2 import cof55
import core
np.set_printoptions(precision=2,linewidth=220)
rg=np.random.default_rng(1)
def Lr(B,r):
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
def diag(B,rg):
    B=onb(B); ds=defect(B,n=60)
    Mb=embed(B).reshape(len(B),25); rows=[]
    for _ in range(90):
        c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); rows.append(cof55(np.ones((5,5))+(c@Mb).reshape(5,5)))
    s=np.linalg.svd(np.array(rows),compute_uv=False)
    return ds, s
bases=[]
Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP['ex1']()]); bases.append(('ex1 col 0',onb(Lr(Bm.transpose(0,2,1),0))))
Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP['ex3']()]); bases.append(('ex3 col 4',onb(Lr(Bm.transpose(0,2,1),4))))
bases.append(('d5_s15',onb(np.load('../rows/clm_p4_d5_defect2_s15.npy'))))
bases.append(('d5_s9',onb(np.load('../rows/clm_p4_d5_defect2_s9.npy'))))
k=0
for name,M in bases:
    E=E0(M,rg); D=complement(M,E); m=6-len(M)
    for trial in range(4):
        c,B=solve_ext(M,D,m,rg,iters=400)
        if c<1e-9:
            ds,s=diag(B,rg); np.save('ext_%d.npy'%k,onb(B)); k+=1
            print(name,'res %.1e'%c,'defect sv',ds[:5],'| gradient-span sv tail',s[12:19])
