# verify2 r12: exact samples of a reg2 special-locus deformation: 22_2 at (m3,m4) = (1,1), row 0 -> 3 (certify_defo: generic dim 10, gcd 10368)
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[0])
def member(t):
    t=F(t); Bs=[]
    for v,Jv in (([0,0,-1,1,0],[0,0,1,1,-2]),([0,0,-1,0,1],[0,0,-1,2,-1])):
        M=[[F(0)]*5 for _ in range(4)]
        for k in range(5): M[0][k]=F(v[k]); M[3][k]+=t*Jv[k]
        Bs.append(M)
    Bs+=[outer_row(1,[4,-1,-1,-1,-1]),outer_row(1,[-3,-3,2,2,2]),outer_col([1,0,-1,0],0),outer_col([0,0,1,-1],0)]
    return Bs
for t in (2,F(1,3),-5): run('22_2 (1,1) row0->3 t=%s'%t,member(t))
