# Round 19: brute-force check of the mixed P_k formulas used in the rank-one lemma (sum over distinct rows and columns, one entry per matrix).
import itertools, numpy as np
rng=np.random.default_rng(3)
def mixed(Ms):
    k=len(Ms); tot=0
    for rows in itertools.permutations(range(4),k):
        for cols in itertools.permutations(range(5),k):
            tot+=np.prod([Ms[i][rows[i],cols[i]] for i in range(k)])
    return tot
def r(n,sz=True):
    v=rng.normal(size=n)+1j*rng.normal(size=n); return v-v.mean() if sz else v
P,Q,k,l,c=0,1,2,3,4
x=r(5,False); y=r(5,False); s=x.sum()
G=np.zeros((4,5),complex); G[P]=x; G[Q]=y
u=r(5); U=np.zeros((4,5),complex); U[k]=u
v=r(4); V=np.zeros((4,5),complex); V[:,c]=v
z=x+y
print('P2(G,u)      ', mixed([G,U]), ' formula -<z,u>(+s terms) =', -(z@u) + 0)
print('P2(G,v)      ', mixed([G,V]), ' formula s(vQ-vP)+xc vP+yc vQ =', s*(v[Q]-v[P])+x[c]*v[P]+y[c]*v[Q] if abs(y.sum()+s)<1e-12 else 'needs sum y=-s')
y2=y-(y.sum()+s)/5; G2=G.copy(); G2[Q]=y2; z2=x+y2
print('P2(G,v) sy=-s', mixed([G2,V]), ' formula', s*(v[Q]-v[P])+x[c]*v[P]+y2[c]*v[Q])
print('P3(G,G,v)/2  ', mixed([G2,G2,V])/2, ' formula -(vP+vQ)(s(xc-yc)+2xc yc - (s^2+<x,y>)) =', -(v[P]+v[Q])*(s*(x[c]-y2[c])+2*x[c]*y2[c]-(s*s+x@y2)))
uc=u.copy(); uc[c]=0; uc-=0; uc[[a for a in range(5) if a!=c]]-=uc.sum()/4; Uc=np.zeros((4,5),complex); Uc[k]=uc
print('P3(G,u,v)    ', mixed([G2,Uc,V]), ' formula (vP+vk)<x,u>+(vQ+vk)<y,u> (u_c=0) =', (v[P]+v[k])*(x@uc)+(v[Q]+v[k])*(y2@uc))
w=r(5); Wm=np.zeros((4,5),complex); Wm[l]=w
print('P3(G,u,w)    ', mixed([G2,U,Wm]), ' formula 2 sum z u w - <z,u>sum w.. (needs <u,w>=0):', 2*np.sum(z2*u*w)-(u@w)*z2.sum()-(z2@u)*w.sum()-(z2@w)*u.sum())
print('P3(G,G,u)/2  ', mixed([G2,G2,U])/2, ' formula s<x,u> - s<y,u> + 2 sum x y u - <x,y> sum u ... =', s*(x@u)-s*(y2@u)+2*np.sum(x*y2*u))
