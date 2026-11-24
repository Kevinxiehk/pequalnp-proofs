# DR2 family, support pattern (2,2|2): rows 0,1 carry 2-dim single-row parts, column 0 a 2-dim single-column part.
#   U_0 = {w : w_0 = 0, sum w = 0, <mu,w> = 0}, mu = (0,1,m3,m4) on columns 1..4 (chart mu_1 != mu_2);  U_1 = (U_0 + C1)^perp cap 1^perp;
#   V = {x : x_1 = 0, sum x = 0}.   The level equations cut out the admissible (m3,m4).
# Tests: 'lev' (dimension of the family), 'cal' (rho = e_0 must be NON-unit), 'om' (Omega inside span(1,e_0): charts rho_j = 1, j = 1..4).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
p=int(sys.argv[1]) if len(sys.argv)>1 else 0; mode=sys.argv[2] if len(sys.argv)>2 else 'none'
def basis(R,V):
    c=R.const; m3=V('m3'); m4=V('m4'); S=add(add(c(1),m3),m4)
    Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    B1=Z(); B1[0][1]=add(m3,c(-1)); B1[0][2]=scal(m3,-1); B1[0][3]=c(1)
    B2=Z(); B2[0][1]=add(m4,c(-1)); B2[0][2]=scal(m4,-1); B2[0][4]=c(1)
    B3=Z(); B3[1][0]=c(4); 
    for j in range(1,5): B3[1][j]=c(-1)
    B4=Z(); B4[1][0]=scal(S,-1); B4[1][1]=scal(S,-1); B4[1][2]=add(c(5),scal(S,-1)); B4[1][3]=add(scal(m3,5),scal(S,-1)); B4[1][4]=add(scal(m4,5),scal(S,-1))
    B5=Z(); B5[0][0]=c(1); B5[2][0]=c(-1)
    B6=Z(); B6[2][0]=c(1); B6[3][0]=c(-1)
    return [B1,B2,B3,B4,B5,B6]
t0=time.time(); F=Family(['m3','m4'],basis,6); W=F.W
print('level equations %d, FO equations %d (%.1f s)'%(len(F.level),len(F.fo),time.time()-t0),flush=True)
if mode=='lev':
    for q in F.level[:12]: print('   ',to_str_Q(q,F.names))
    print(F.run([],p,'dr22lev',fo=False))
elif mode=='cal':
    norm=[F.eq('r0',1)]+[W('r%d'%j) for j in range(1,5)]
    print('CALIBRATION rho = e_0:',F.run(norm,p,'dr22cal'))
elif mode=='elim':
    import subprocess
    jr=int(sys.argv[3]); s=W('r1')
    for j in range(2,5): s=add(s,W('r%d'%j))
    polys=F.fo+[s,F.eq('r%d'%jr,1)]
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    elimv='*'.join(F.xv+F.rv)
    script='ring R=%d,(%s),dp;\nideal I=%s;\nideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nprint("FACTORS");\nint i; for(i=1;i<=size(J);i++){print(factorize(J[i]));}\nquit;\n'%(p,','.join(F.names),',\n'.join(lines),elimv)
    open('/tmp/elim.sing','w').write(script)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/elim.sing'),capture_output=True,text=True,timeout=150)
    print(r.stdout[:3000]); print(r.stderr[:500])
elif mode=='e0':
    import subprocess
    zero=['x03','x04','x10','x11','x12','x20','x30']; res={}
    for xn in [v for v in F.xv if v not in zero]:
        polys=F.fo+[W(r) for r in F.rv]+[W(z) for z in zero]+[F.eq(xn,1)]
        lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
        script='ring R=%d,(%s),dp;\nideal I=%s;\nideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nquit;\n'%(p,','.join(F.names),',\n'.join(lines),'*'.join(F.xv+F.rv))
        open('/tmp/elim0.sing','w').write(script)
        r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/elim0.sing'),capture_output=True,text=True,timeout=100)
        out=' '.join(r.stdout.split()); res.setdefault(out,[]).append(xn)
    for k,v in res.items(): print('elimination ideal [%s] for charts %s'%(k,v))
elif mode=='om':
    ok=True
    for jr in range(1,5):
        s=W('r1')
        for j in range(2,5): s=add(s,W('r%d'%j))
        u,n,sec=F.run([s,F.eq('r%d'%jr,1)],p,'dr22om'); ok=ok and bool(u)
        print('chart sum_{j>=1} rho_j = 0, rho_%d = 1: unit=%s size %s (%.1f s)'%(jr,u,n,sec),flush=True)
    print('prime %d:'%p,'ALL CHARTS UNIT' if ok else 'NOT ALL UNIT')
