# Sanity checks of the rigorous statements in NOTES-reg2 (numerical, on the known 7-dim level spaces and on rc45 / NC spaces).
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, itertools
from t import *
from a1 import embed, Phi, defect
from a5 import onb, rref_tol
from a6 import T1, E0
from r5_FO2 import cof55
import core
rg=np.random.default_rng(11)
def Lr(B,r):
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
def F45(Y):
    A=np.ones((5,5),complex); A[:4]+=Y; return perm(A)
def Nvec(X):  # N_j(X) = perm_4(X minus column j)
    return np.array([perm(np.delete(X,j,axis=1)) for j in range(5)])
def dF(X,Z,h=1e-6): return (F45(X+h*Z-1)-F45(X-h*Z-1))/(2*h)   # F45 adds J'
worst={'tau':0,'Phi':0,'colscale':0,'crit':0}; nline=0; tight=0
for name in core.SP:
    B=np.array([np.array(mm,dtype=complex) for mm in core.SP[name]()]); d=len(B)
    for tr,Bt in (('row',B),('col',B.transpose(0,2,1))):
        # put row r last by permuting rows so that 'embed' convention (row 4 = r) applies
        for r in range(5):
            order=[i for i in range(5) if i!=r]+[r]; Bp=Bt[:,order,:]
            M=Lr(Bp,4)
            if len(M)==0: continue
            M=onb(M); nline+=1
            # (1) tau_r in T_1(M): D_tau perm(J+Y)=0
            tau=np.ones((5,5),complex); tau[4]=-4
            for _ in range(3):
                c=rg.normal(size=len(M))+1j*rg.normal(size=len(M)); Y=np.einsum('k,kab->ab',c,M)
                g=cof55(np.ones((5,5))+embed(Y[None])[0]).reshape(5,5); worst['tau']=max(worst['tau'],abs((g*tau).sum())/np.abs(g).max())
                # (2) Phi(Y) perp row-r projection of L^ (incl. the all-ones row)
                ph=Phi(Y); W=np.concatenate([Bp[:,4,:],np.ones((1,5))],0); worst['Phi']=max(worst['Phi'],np.abs(W@ph).max()/(1e-30+np.abs(ph).max()+1))
                # (3) column-scaling identity <s,N(X)> = (sum s)F(X) - D_{X D_s}F(X), X = J'+Y
                s=rg.normal(size=5)+1j*rg.normal(size=5); X=np.ones((4,5))+Y
                lhs=(s*Nvec(X)).sum(); rhs=s.sum()*F45(Y)-dF(X,X*s[None,:]); worst['colscale']=max(worst['colscale'],abs(lhs-rhs)/abs(lhs))
            # (4) criterion: dim W_r <= dim Omega(M) - 1
            T=T1(embed(M),rg); rho=T[:,4,:]; dOm=rank(rho,1e-7); w=rank(Bp[:,4,:])
            if w>dOm-1: worst['crit']+=1
            if w==dOm-1: tight+=1
print('lines checked',nline,'violations of criterion',worst['crit'],'tight',tight)
print('max |D_tau perm| (rel) %.1e ; max |<row r, Phi(Y)>| %.1e ; column-scaling identity rel err %.1e'%(worst['tau'],worst['Phi'],worst['colscale']))
