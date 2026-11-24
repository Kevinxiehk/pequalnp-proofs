# DOUBLE-BLOCK family (NOTES-reg2 14.8): U = {(al,be,g,g,g) : al+be+3g = 0} (row 0), column skew block {x e_0^T + a (Jx) e_1^T : x in V}
# (V = {x_0 = 0, sum = 0}), row skew block {e_2 w^T + b e_3 (J'w)^T : w sum-zero on columns 2,3,4}, J' the rotation on columns 2,3,4.
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
def basis(R,V):
    c=R.const; a=V('a'); b=V('b'); Z=lambda: [[{} for _ in range(5)] for _ in range(4)]; Bs=[]
    for u in ([c(3),{},c(-1),c(-1),c(-1)],[{},c(3),c(-1),c(-1),c(-1)]):
        B=Z(); B[0]=u; Bs.append(B)
    for x in ([{},c(1),c(-1),{}],[{},{},c(1),c(-1)]):
        Jx=[{},add(x[2],x[3],-1),add(x[3],x[1],-1),add(x[1],x[2],-1)]; B=Z()
        for i in range(4):
            if x[i]: B[i][0]=x[i]
            if Jx[i]: B[i][1]=mul(a,Jx[i])
        Bs.append(B)
    for w in ([c(-1),c(1),{}],[{},c(-1),c(1)]):
        Jw=[add(w[1],w[2],-1),add(w[2],w[0],-1),add(w[0],w[1],-1)]; B=Z()
        for j in range(3):
            if w[j]: B[2][2+j]=w[j]
            if Jw[j]: B[3][2+j]=mul(b,Jw[j])
        Bs.append(B)
    return Bs
F=Family(['a','b'],basis,6)
lv=[to_str_Q({k[:2]:v for k,v in q.items()},['a','b']) for q in F.level]
print('level equations:',len(lv))
if lv:
    open('/tmp/blk2.sing','w').write('LIB "primdec.lib";\nring R=0,(a,b),dp;\nideal I=%s;\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}\nquit;\n'%','.join('('+l+')' for l in lv))
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/blk2.sing'),capture_output=True,text=True)
    print(' '.join(l for l in r.stdout.split('\n') if 'redefin' not in l)[:1500])
