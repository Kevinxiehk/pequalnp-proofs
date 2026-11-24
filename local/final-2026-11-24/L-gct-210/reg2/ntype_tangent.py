# Round 15: is ntype1 isolated inside its combinatorial type "(1,1|2) + N + R1"?  Unknowns: u0, u3 (rows 0, 3), v1, v2 (column 0 plane, C^4),
# lam, x (R1 = e_1 x + e_2 lam x), a, b (N = e_1 a + e_2 b): 5+5+8+1+5+5+5 = 34.  Residual = F(J'+Y) - 120 at random Y in the span.  The
# dimension of the solution set at ntype1 = 34 - rank(Jacobian) - (gauge = 3 scalings + 4 (GL2 on V) + 2 (N -> mu N + nu R1)) if smooth.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
w=np.exp(2j*np.pi/3)
z0=np.concatenate([[0,1,w,w*w,0],[0,w*w,1,w,0],[-2,1,1,0],[-1,0,0,1],[-1],[0,w,1,w*w,0],[0,w+2,1-w,0,-1],[0,w*w-1,w-1,0,1]]).astype(complex)
def build(z):
    u0,u3,v1,v2,lam,x,a,b=z[0:5],z[5:10],z[10:14],z[14:18],z[18],z[19:24],z[24:29],z[29:34]
    E=np.zeros((6,4,5),complex)
    E[0,0]=u0; E[1,3]=u3; E[2,:,0]=v1; E[3,:,0]=v2; E[4,1]=x; E[4,2]=lam*x; E[5,1]=a; E[5,2]=b
    return E
rg=np.random.default_rng(0); C=rg.normal(size=(300,6))+1j*rg.normal(size=(300,6))
def res(z): return F45(np.einsum('nk,kij->nij',C,build(z)))-120
r0=res(z0); print('level residual at ntype1: %.1e'%np.abs(r0).max())
J=np.empty((len(r0),34),complex); h=1e-7
for k in range(34):
    zp=z0.copy(); zp[k]+=h; zm=z0.copy(); zm[k]-=h; J[:,k]=(res(zp)-res(zm))/(2*h)
s=np.linalg.svd(J,compute_uv=False); print('singular values (tail):',np.round(s[-14:]/s[0],10))
rk=int((s>1e-7*s[0]).sum()); print('rank J =',rk,' kernel dim =',34-rk,' -> family dimension (minus gauge 9) =',34-rk-9)
# --- follow the non-gauge tangent directions: step along a kernel vector, project back (Gauss-Newton with gauge-fixing normalisations)
u_,s_,vh=np.linalg.svd(J); K=vh[rk:].conj()          # kernel basis (11 x 34)
gauge_idx=[1,7,19, 10,11,14,15, 29,30]   # fix: u0_1=1, u3_2=1, x_1=w ... (coordinates frozen at ntype1 values)
from scipy.optimize import least_squares
def resfix(zr,zfix_idx,zfix_val):
    z=np.empty(34,complex); free=[k for k in range(34) if k not in zfix_idx]
    z[free]=zr[:len(free)]+1j*zr[len(free):]; z[zfix_idx]=zfix_val
    r=res(z); return np.concatenate([r.real,r.imag])
free=[k for k in range(34) if k not in gauge_idx]
for trial in range(3):
    dirn=K.T@(rg.normal(size=len(K))+1j*rg.normal(size=len(K))); z1=z0+0.05*dirn/np.linalg.norm(dirn)
    zr=np.concatenate([z1[free].real,z1[free].imag])
    sol=least_squares(resfix,zr,args=(gauge_idx,z1[gauge_idx]),method='lm',max_nfev=3000)
    z=np.empty(34,complex); z[free]=sol.x[:len(free)]+1j*sol.x[len(free):]; z[gauge_idx]=z1[gauge_idx]
    E=build(z); print('trial',trial,': residual %.1e, distance from ntype1 %.3f'%(np.abs(res(z)).max(),np.linalg.norm(z-z0)))
    print('   u0 =',np.round(z[0:5],3),' u3 =',np.round(z[5:10],3)); print('   x =',np.round(z[19:24],3),' lam =',np.round(z[18],3),' col-4 of a,b:',np.round([z[28],z[33]],3))
    np.save('/home/kevxhk/work/L-gct-210/reg2/p111/ntype_member_%d.npy'%trial,E)
