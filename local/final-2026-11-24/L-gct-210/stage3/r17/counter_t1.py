# Round 17: dim T_1 and FO2_0 bound of the (PR2-split') counterexample N = X (+) e_3 (x) Z (generic member of the family), embedded in 5x5.
# A 9-dim level L with a_r = 1 needs L_r = N with dim T_1(N) >= 10 and FO2_0(N) >= 9.
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r10'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
src=open('/home/kevxhk/work/L-gct-210/stage3/r10/t1_census5.py').read().split('cnt={}')[0]
exec(src)
def member(rho,y,z):
    xb=np.zeros((4,5),complex); xb[0,0]=-1; xb[1,0]=1; xb[1,1:]=y
    xc=np.zeros((4,5),complex); xc[0,0]=-1; xc[2,0]=1; xc[2,1:]=z
    xd=np.zeros((4,5),complex); xd[0,0]=1; xd[1,0]=rho; xd[2,0]=-1-rho
    # Z = (span(0,y),(0,z)) + C1)^perp, 2-dim
    A=np.array([[1,1,1,1,1],np.r_[0,y],np.r_[0,z]]); u,s,vh=np.linalg.svd(A); Zb=vh[3:].conj()
    zs=[]
    for zz in Zb:
        t=np.zeros((4,5),complex); t[3]=zz; zs.append(t)
    return np.array([xb,xc,xd]+zs)
cases={'simple y=(1,-1,0,0), z=(0,0,1,-1)':(1.7,np.array([1,-1,0,0.]),np.array([0,0,1,-1.]))}
# a less special member: y o z in span(y,z): take y=(1,a,b,c) generic? use y,z with disjoint supports variants
cases['y=(2,-1,-1,0), z=(0,1,-1,0)']=(0.3+0.4j,np.array([2,-1,-1,0.]),np.array([0,1,-1,0.]))
for nm,(rho,y,z) in cases.items():
    Z4=member(rho,y,z); B=np.zeros((5,5,5),complex); B[:,:4,:]=Z4
    print(nm,' check',build7.check(B,n=3),' <y,z>',y@z, ' yoz in span?',np.linalg.matrix_rank(np.array([y,z,y*z]),1e-9))
    t=T1(B); n_,b0=fo2_0(B); print('   dim T_1 =',t[0],'(gaps %.0e/%.0e)'%(t[1],t[2]),'  FO2_0 bound =',b0)
# random members: y random (sum 0), z_j = y_j/(y_j - be) with sum_j y_j/(y_j - be) = 0 (then <y,z> = 0 automatically, y o z = be z + y)
rg=np.random.default_rng(11)
for trial in range(4):
    y=rg.normal(size=4)+1j*rg.normal(size=4); y-=y.mean()
    # polynomial in be: sum_j y_j prod_{k != j} (y_k - be) = 0
    P=np.poly1d([0])
    for j in range(4):
        q=np.poly1d([y[j]])
        for k in range(4):
            if k!=j: q=q*np.poly1d([-1,y[k]])
        P=P+q
    for be in P.roots[:1]:
        z=y/(y-be); rho=rg.normal()+1j*rg.normal()
        Z4=member(rho,y,z); B=np.zeros((5,5,5),complex); B[:,:4,:]=Z4
        t=T1(B); n_,b0=fo2_0(B)
        print('random member %d: level check %.1e  sum z %.1e <y,z> %.1e  dim T_1 = %d (gaps %.0e/%.0e)  FO2_0 = %d'%(trial,build7.check(B,n=3),abs(z.sum()),abs(y@z),t[0],t[1],t[2],b0))
