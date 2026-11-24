# Round 12, target 2: classify the 19 rows-team (6,3) spaces (clm_p4_d6_defect3_*, nc_d6_k1_*, seed_d6_e3_*) by line pattern and genuine parts.
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
exec(open('/home/kevxhk/work/L-gct-210/reg2/mech_census.py').read().split("sig=collections.Counter()")[0].split("src=open")[0])
def rk(A,tol=1e-6): return np.linalg.matrix_rank(A,tol=tol) if len(A) else 0
def span(A):
    if len(A)==0: return np.zeros((0,20),complex)
    u,s,vh=np.linalg.svd(A.reshape(len(A),-1)); return vh[:int((s>1e-6*max(1,s[0])).sum())]
def inter_dim(A,B): return rk(A)+rk(B)-rk(np.concatenate([A,B],0)) if len(A) and len(B) else 0
files=sorted(glob.glob('../rows/clm_p4_d6_defect3_*.npy')+glob.glob('../rows/nc_d6_k1_*.npy')+glob.glob('../rows/seed_d6_e3_*.npy'))
for f in files:
    M=np.load(f); M=M/np.abs(M).max()
    lines=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; lines.append(sub_supported(M,m))
    for c in range(5):
        m=np.zeros((4,5),bool); m[:,c]=True; lines.append(sub_supported(M,m))
    Lin=span(np.concatenate([l.reshape(len(l),-1) for l in lines if len(l)]+[np.zeros((0,20))],0)); e=len(Lin)
    parts=[]
    for (kind,a,b) in [('R',r,j) for r in range(4) for j in range(r+1,4)]+[('C',a,b) for a in range(5) for b in range(a+1,5)]:
        m=np.zeros((4,5),bool)
        if kind=='R': m[a]=True; m[b]=True
        else: m[:,a]=True; m[:,b]=True
        P=sub_supported(M,m)
        if len(P)==0: continue
        Pf=span(P); g=len(Pf)-inter_dim(Pf,Lin)
        if g>0: parts.append('%s%d%d:g%d'%(kind,a,b,g))
    print('%-40s e=%d rows %s cols %s | %s'%(f.split('/')[-1],e,[len(l) for l in lines[:4]],[len(l) for l in lines[4:]],' '.join(parts)))
