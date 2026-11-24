# verify2 r11: my own exact (Fractions) re-certification of reg2's special points (BB p = -1/2, x = (0,0,1,-1), p = +-1; 8 BD points)
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[0])
U0=[outer_row(0,[1,-1,0,0,0]),outer_row(0,[1,0,-1,0,0])]; U1=[outer_row(1,[-1,-1,-1,4,-1]),outer_row(1,[-1,-1,-1,-1,4])]
for x in ([1,0,F(-1,2),F(-1,2)],[0,0,1,-1],[1,0,1,-2],[1,0,-1,0]):
    x=[F(t) for t in x]; xp=[x[2]-x[3],0,x[3]-x[0],x[0]-x[2]]
    run('BB x=%s'%[str(t) for t in x],U0+U1+[outer_col(x,3),outer_col(xp,4)])
for (a,b) in [(-1,1),(-3,1),(1,1),(1,-3),(F(-1,3),F(-1,3)),(0,-1),(1,-1),(-1,-1)]:
    v=[F(1),F(a),F(b),F(0),-1-F(a)-F(b)]; W=null([[1]*5,[0,0,0,1,0],v],5)
    run('BD v=%s'%[str(t) for t in v],[outer_row(0,w) for w in W]+[outer_row(1,[-1,-1,-1,4,-1]),outer_row(1,v),outer_col([2,0,-1,-1],3),outer_col([0,0,1,-1],4)])
