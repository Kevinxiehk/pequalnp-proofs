# verify2 r12: exact samples of reg2 15.3 BB row deformations: row 0 -> {e_0 w + t e_j (J w)}, w sum-zero on columns 0,1,2, J = rotation
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[0])
def bbdef(p,t,j):
    p=F(p); t=F(t); x=[F(1),F(0),p,-1-p]; xp=[x[2]-x[3],F(0),x[3]-x[0],x[0]-x[2]]
    Bs=[]
    for w in ([1,-1,0,0,0],[0,1,-1,0,0]):
        Jw=[w[1]-w[2],w[2]-w[0],w[0]-w[1],0,0]
        M=[[F(0)]*5 for _ in range(4)]
        for k in range(5): M[0][k]=F(w[k]); M[j][k]+=t*Jw[k]
        Bs.append(M)
    Bs+=[outer_row(1,[-1,-1,-1,4,-1]),outer_row(1,[-1,-1,-1,-1,4]),outer_col(x,3),outer_col(xp,4)]
    return Bs
for (p,t,j) in [(2,3,1),(2,3,2),(F(-1,2),1,1),(1,1,2),(F(-3,5),F(7,2),1)]:
    run('BBdef j=%d p=%s t=%s'%(j,p,t),bbdef(p,t,j))
