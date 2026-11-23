# Pattern (2,1,1|2), incidence case (iii): V = {x : x_1 = 0, sum x = 0} (column 0), U_0 = {w : w_0 = 0, sum w = 0, <mu,w> = 0} in row 0,
#   row 2: w_2 = mu - mean_4(mu) (H-orthogonal complement of U_0, zero at column 0), row 1: w_1 = 5 e_0 - 1.   chart mu = (0,1,m3,m4).
# modes: lev | cal | elim J | e0
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2/gb')
from famtool import *
import subprocess
p=int(sys.argv[1]); mode=sys.argv[2]
def basis(R,V):
    c=R.const; m3=V('m3'); m4=V('m4'); S=add(add(c(1),m3),m4)
    Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    B1=Z(); B1[0][1]=add(m3,c(-1)); B1[0][2]=scal(m3,-1); B1[0][3]=c(1)
    B2=Z(); B2[0][1]=add(m4,c(-1)); B2[0][2]=scal(m4,-1); B2[0][4]=c(1)
    B3=Z(); B3[1][0]=c(4)
    for j in range(1,5): B3[1][j]=c(-1)
    B4=Z(); B4[2][1]=scal(S,-1); B4[2][2]=add(c(4),scal(S,-1)); B4[2][3]=add(scal(m3,4),scal(S,-1)); B4[2][4]=add(scal(m4,4),scal(S,-1))
    B5=Z(); B5[0][0]=c(1); B5[2][0]=c(-1)
    B6=Z(); B6[2][0]=c(1); B6[3][0]=c(-1)
    return [B1,B2,B3,B4,B5,B6]
F=Family(['m3','m4'],basis,6); W=F.W
print('level equations %d, FO equations %d'%(len(F.level),len(F.fo)),flush=True)
def sing(polys,elim=None):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    body='ideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);'%elim if elim else 'ideal J=std(I);\nprint(J);'
    script='ring R=%d,(%s),dp;\noption(redSB);\nideal I=%s;\n%s\nquit;\n'%(p,','.join(F.names),',\n'.join(lines),body)
    open('/tmp/s211.sing','w').write(script)
    r=subprocess.run(['/home/claude/tools/gb/Singular','-q'],stdin=open('/tmp/s211.sing'),capture_output=True,text=True,timeout=120)
    return ' '.join(r.stdout.split())
if mode=='lev':
    lines=[to_str_Q(q,F.names) for q in F.level]
    script='ring R=%d,(m3,m4),dp;\noption(redSB);\nideal I=%s;\nideal J=std(I);\nprint(J);\nprint("dim");print(dim(J));print("primdec");LIB "primdec.lib";print(minAssGTZ(J));quit;\n'%(p,',\n'.join(l for l in lines if l!='0') if lines else '0')
    open('/tmp/s211.sing','w').write(script)
    r=subprocess.run(['/home/claude/tools/gb/Singular','-q'],stdin=open('/tmp/s211.sing'),capture_output=True,text=True,timeout=120); print(r.stdout[:1500])
elif mode=='cal':
    print('CALIBRATION rho = e_0:',sing(F.level+F.fo+[F.eq('r0',1)]+[W('r%d'%j) for j in range(1,5)])[:200])
elif mode=='elim':
    for jr in range(1,5):
        s=W('r1')
        for j in range(2,5): s=add(s,W('r%d'%j))
        print('rho-chart %d: elimination ideal: %s'%(jr,sing(F.level+F.fo+[s,F.eq('r%d'%jr,1)],'*'.join(F.xv+F.rv))))
elif mode=='e0':
    for tag,z in (('N1 (x21 = 0, valid for S != 0)','x21'),('N2 (x22 = 0, valid for S != 4)','x22')):
        zero=['x03','x04','x10','x11',z,'x20','x30']; res={}
        for xn in [v for v in F.xv if v not in zero]:
            out=sing(F.level+F.fo+[W(r) for r in F.rv]+[W(v) for v in zero]+[F.eq(xn,1)],'*'.join(F.xv+F.rv)); res.setdefault(out,[]).append(xn)
        for k,v in res.items(): print('%s: elimination ideal [%s] for %d charts %s'%(tag,k,len(v),v if k!='1' else ''))
