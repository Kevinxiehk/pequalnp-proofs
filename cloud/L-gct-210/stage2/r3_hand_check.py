# Round 3: numerical confirmation of the two hand computations that kill the 12 remaining exception configurations.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import nullspace, rank
import r3_survey as RS, r3_cube2 as RC
rng=np.random.default_rng(5)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
def F(rows):
    v=np.zeros((3,5),complex)
    for i,vec in rows: v[i]=vec
    return v.reshape(-1)
one=np.ones(5); z=np.zeros(5)
def cube_test(A0,n,u,S):
    cols=[i*5+j for i in range(3) for j in S]
    Nb=nullspace(np.vstack([A0[:,cols],n[cols][None,:]])); d=Nb.shape[1]
    vs=[Nb@rnd(d) for _ in range(6)]; ell=np.array([v[:3].sum() for v in vs]); pm=np.array([RC.perm3(v.reshape(3,3)*u[:,list(S)]) for v in vs])
    B1=np.abs(ell).max()>1e-9
    defect=max(abs(pm[i]*ell[j]**3-pm[j]*ell[i]**3)/(abs(pm[i]*ell[j]**3)+abs(pm[j]*ell[i]**3)+1e-300) for i in range(6) for j in range(i+1,6))
    return d,B1,defect,vs,ell,pm
print('(a) conjugate family: n** = sum_{Q_1}(tau_2 - i tau_3) + (1-i) sum_{Q_2} tau_2 - delta*ell')
for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
    cells=np.array([0]*comp[0]+[1]*comp[1]+[2]*comp[2]); s12=(tuple(cells),1); s13=(tuple(cells),-1)
    w2,A1,A2,y12=RS.typeII(*s12); w3,B1v,B3,y13=RS.typeII(*s13)
    A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1v+y13*one),(2,B3)])]); u=np.array([one,1/w2,1/w3])
    q1=(cells==0).astype(float); q2=(cells==1).astype(float)
    # is the hand candidate inside the numerically found leaf?
    A0b,ub,sols,triv=RC.leaves(s12,s13)
    m_hand=np.concatenate([q1+(1-1j)*q2,-1j*q1])
    inleaf=[rank(np.hstack([V,m_hand[:,None]]))==rank(V) for V in sols]
    S=(int(np.where(cells==0)[0][0]),int(np.where(cells==1)[0][0]),int(np.where(cells==2)[0][0]))
    out=[]
    for delta in (0.0,0.37+0.2j,rnd(1)[0]):
        n=F([(1,q1+(1-1j)*q2-delta*one),(2,-1j*q1)]); d,B1,defect,vs,ell,pm=cube_test(A0,n,u,S)
        extra=''
        if delta==0.0:
            c1=np.array([v[2] for v in vs]); extra=' perm/(c_1 ell^2) = '+str(np.round(pm/(c1*ell**2),6)[:3])
        out.append('delta=%s: dim Pi_S=%d, ell!=0:%s, cube defect %.2f%s'%(np.round(delta,2),d,B1,defect,extra))
    print(' cells',tuple(cells),' #leaves',len(sols),' hand candidate in leaf:',inleaf,' leaf dims',[V.shape[1] for V in sols]); [print('     ',o) for o in out]
print('(b) non-conjugate families A and C: coefficient test on S = (two columns of the 2-cell, Q_3 column)')
for name,s12,s13,pair,extra_cols in (('A',((0,0,0,1,2),1),((0,1,1,0,2),1),(1,2),[(1,0),(1,3)]),('C',((0,0,1,1,2),1),((1,1,0,0,2),1),(0,1),[(1,2),(1,3)])):
    w2,A1,A2,y12=RS.typeII(*s12); w3,B1v,B3,y13=RS.typeII(*s13)
    A0=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1v+y13*one),(2,B3)])]); u=np.array([one,1/w2,1/w3])
    A0b,ub,sols,triv=RC.leaves(s12,s13)
    S=(pair[0],pair[1],4); res=[]
    for t in range(4):
        m3=np.zeros(5,complex); m3[pair[0]]=1; m3[pair[1]]=-1
        m2=np.zeros(5,complex)
        for (r_,c_) in extra_cols: m2[c_]=rnd(1)[0]
        delta=rnd(1)[0]; n=F([(1,m2-delta*one),(2,m3)])
        m=np.concatenate([m2,m3]); inleaf=any(rank(np.hstack([V,m[:,None]]))==rank(V) for V in sols)
        d,B1,defect,vs,ell,pm=cube_test(A0,n,u,S); res.append((inleaf,d,B1,round(defect,2)))
    print(' config',name,' #leaves',len(sols),'leaf dims',[V.shape[1] for V in sols],' (candidate in leaf, dim Pi_S, ell!=0, cube defect):',res)
