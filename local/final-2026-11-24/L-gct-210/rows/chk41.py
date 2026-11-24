import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
import numpy as np, glob
from clm import *
from seeded import defect_basis
from core import ext_space, fresh_check, Pk
np.set_printoptions(precision=3,suppress=True,linewidth=200)
# (1) every (4,1) solution: is the free-row element of L' equal to e_i m^T ?
for f in sorted(glob.glob('clm_p4_d4_defect1_s*.npy'))+sorted(glob.glob('seed_d4_e1_t*.npy')):
    Z=np.load(f); d=len(Z); m=defect_basis(Z,1)[0]
    u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Q=vh.reshape(d,4,5); out=[]
    for i in range(4):
        A=np.delete(Q,i,axis=1).reshape(d,-1); uu,ss,vv=np.linalg.svd(A)
        for k in range(d):
            if ss[k]<1e-7:
                y=np.einsum('k,kab->ab',uu[:,k].conj(),Q)[i]   # row i of the element supported on row i
                ang=abs(np.vdot(y,m))/np.linalg.norm(y)/np.linalg.norm(m); out.append((i,round(float(ang),6)))
    print(f,'free-row elements (row, |cos| with defect line m):',out, ' zero entries of m:',[j for j in range(5) if abs(m[j])<1e-7*np.abs(m).max()])
# (2) exact family L_m: first-order extension space
def Lm(m,c=0.0):
    m=np.array(m,complex); B=[]
    M=np.zeros((5,5),complex); M[2]=m; B.append(M)
    A=np.array([np.ones(5),m]); u,s,vh=np.linalg.svd(A); 
    for w in vh[2:].conj():
        M=np.zeros((5,5),complex); M[4]=w; B.append(M)
    for x,ph in (([1,0,0,-1,0],[0,c,-c,0,0]),([0,1,0,-1,0],[0,c,-2*c,c,0])):
        M=np.zeros((5,5),complex); M[:,2]=x; M[:,4]=ph; B.append(M)
    M=np.zeros((5,5),complex); M[:,4]=[1,1,-3,1,0]; B.append(M); return np.array(B)
for m,c in (([1,2,-4,1,0],0.0),([1,2,-4,1,0],1.0),([1,1j,-1,-1j,0],0.0),([1,-1,0,0,0],0.0)):
    B=Lm(m,c); dE,E,s=ext_space(B)
    print('L_m m=%s c=%s: dim %d fresh P_k %.1e dim E = %d (sing. values around the cut: %.1e | %.1e)'%(m,c,np.linalg.matrix_rank(B.reshape(7,-1)),fresh_check(B),dE,s[24-dE],s[25-dE] if 25-dE<len(s) else 0))
