# verify2 r11: exact sample checks of (2,1,1|1,1) members (reg2 13.9-13.10), my generator
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[0])
def cols(x,xp): return [outer_col(x,3),outer_col(xp,4)]
# (I-a): U_0 = {w3 = w4 = 0}, u1 = (-1,-1,-1,0,3), u2 = (-1,-1,-1,4,-1), x = (1,-2,0,1), x' = (1,0,0,-1)   [reg2: (9,3,7)]
U0=null([[1]*5,[0,0,0,1,0],[0,0,0,0,1]],5)
run('(I-a)',[outer_row(0,w) for w in U0]+[outer_row(1,[-1,-1,-1,0,3]),outer_row(2,[-1,-1,-1,4,-1])]+cols([1,-2,0,1],[1,0,0,-1]))
# (a,a): U_0 = span(5e3-1, 5e4-1); u1, u2 orthogonal basis of H_34 = {w3 = w4 = 0, sum 0}; x perp x' in {x_0 = 0}
u1=[1,-1,0,0,0]; u2=[1,1,-2,0,0]
for x,xp in (([0,1,2,-3],None),([0,0,1,-1],None),([0,1,-2,1],None)):
    # x' perp x inside {x_0 = 0}: 3-dim space, choose x' = null of [e0, x] intersect with a random extra condition
    xp=null([[1,0,0,0],[1,1,1,1],x],4)[0]
    run('(a,a) x=%s'%x,[outer_row(0,[-1,-1,-1,4,-1]),outer_row(0,[-1,-1,-1,-1,4]),outer_row(1,u1),outer_row(2,u2)]+cols(x,xp))
# (II-2 beta): U_0 = {sum 0, w3 = 0, perp w}, u1 = w = (1,s,-1-s,0,0), u2 = 5e3-1, x = (-2,1,0,1), x' = (0,1,0,-1)   [s = 0: (9,3,7)]
for s in (F(2),F(0),F(-3,2)):
    w=[F(1),s,-1-s,F(0),F(0)]; U0=null([[1]*5,[0,0,0,1,0],w],5)
    run('(II-2b) s=%s'%s,[outer_row(0,v) for v in U0]+[outer_row(1,w),outer_row(2,[-1,-1,-1,4,-1])]+cols([-2,1,0,1],[0,1,0,-1]))
