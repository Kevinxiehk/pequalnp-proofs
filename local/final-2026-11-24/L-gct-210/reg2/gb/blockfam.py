# BLOCK family (NOTES-reg2 14.3): m = (t, 0, -1-t, 1, 0) (zero at the block columns 1, 4), U = {1,m}^perp (row 0), e_2 m^T (row 2),
# block { x e_1^T + a (J x) e_4^T : x in V }, V = {x_0 = 0, sum = 0}, J x = (0, x2-x3, x3-x1, x1-x2) (rows 1..3).  Level variety in (t, a).
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
def basis(R,V):
    c=R.const; t=V('t'); a=V('a'); Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    m=[t,{},add(c(-1),scal(t,-1)),c(1),{}]
    U=[[{},c(1),{},{},c(-1)],[m[2],{},scal(m[0],-1),{},add(m[0],m[2],-1)],[m[3],{},{},scal(m[0],-1),add(m[0],m[3],-1)]]
    Bs=[]
    for w in U:
        B=Z(); B[0]=w; Bs.append(B)
    B=Z(); B[2]=m; Bs.append(B)
    for x in ([{},c(1),c(-1),{}],[{},{},c(1),c(-1)]):
        Jx=[{},add(x[2],x[3],-1),add(x[3],x[1],-1),add(x[1],x[2],-1)]
        B=Z()
        for i in range(4):
            if x[i]: B[i][1]=x[i]
            if Jx[i]: B[i][4]=mul(a,Jx[i])
        Bs.append(B)
    return Bs
F=Family(['t','a'],basis,6)
lv=[to_str_Q({k[:2]:v for k,v in q.items()},['t','a']) for q in F.level]
print('level equations:',len(lv))
open('/tmp/blk.sing','w').write('LIB "primdec.lib";\nring R=0,(t,a),dp;\nideal I=%s;\nI=std(I);\nprint(I);\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}\nquit;\n'%','.join('('+l+')' for l in lv))
r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/blk.sing'),capture_output=True,text=True)
print(' '.join(l for l in r.stdout.split('\n') if 'redefin' not in l)[:1500])
