import numpy as np, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2')
import fo2lib
a,b,c,d,e=0,1,2,3,4
def Mstar(ma,mb,al,be,ga):
    Z=lambda:np.zeros((5,5),complex)
    g1=Z(); g1[a,0]=-1; g1[c,0]=1; g1[c,1]=ma*al; g1[c,4]=-ma*al
    g2=Z(); g2[b,0]=-1; g2[c,0]=1; g2[c,1]=mb*al; g2[c,4]=-mb*al
    g3=Z(); g3[c,0]=1; g3[d,0]=-1
    g4=Z(); g4[c,0]=1; g4[e,0]=-1
    g5=Z(); g5[c,1]=al; g5[c,4]=-al; g5[d,1]=-be; g5[d,2]=be; g5[d,3]=be; g5[d,4]=-be
    g6=Z(); g6[c,1]=al; g6[c,4]=-al; g6[e,2]=-ga; g6[e,3]=ga
    return np.array([g1,g2,g3,g4,g5,g6])
rng=np.random.default_rng(3)
for par in [(1,2,1,1,1),(0,0,1,1,1),(0,1,2,-1,3),(1+2j,-0.5j,0.7,1.3-1j,2j),(3,5,-2,7,1)]:
    dT,r,bd,inT,iso,sg=fo2lib.fo2(Mstar(*par),rng)
    print('M*',par,': dim T_1 = %d, rank = %d, FO2 bound = %d  (M* in T_1: %.1e, isotropic: %.1e, sv %.1e | %.1e)'%(dT,r,bd,inT,iso,sg[r-1],sg[r] if r<len(sg) else 0))
