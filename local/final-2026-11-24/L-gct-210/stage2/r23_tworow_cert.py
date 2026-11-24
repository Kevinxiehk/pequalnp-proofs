# Char-0 certificate (Singular std over QQ) that the two-row level ideal I of a chart has radical = the claimed components:
#  chart A ((3,4), m_4 = 1): one component J;  chart B ((0,1), m_2 = 1): components J1 (m1 = 0), J2 (m2 = 0).
# Tests: (a) I reduces to 0 modulo each J (J contains I); (b) for each generator g of J: 1 in I + (1 - w g)  (g in rad I) [chart A];
# chart B: m1*m2 in rad(I), then generators of J1 in rad(I + (m1)) and of J2 in rad(I + (m2)).
import sys, subprocess, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_tworow_lib.py').read())
def sing_unit(vs,gens,extra_name='w'):
    s='ring R=0,(%s,%s),dp; option(redSB); ideal I=%s; ideal G=std(I); print(reduce(1,G)==0); quit;'%(','.join(map(str,vs)),extra_name,','.join(str(g).replace('**','^') for g in gens))
    r=subprocess.run(['bash','-c','ulimit -v '+__import__('os').environ.get('SING_ULIM','2000000')+'; timeout '+__import__('os').environ.get('SING_TMO','3600')+' Singular -q'],input=s,capture_output=True,text=True); return r.stdout.strip()
def in_ideal(vs,I,Jgens):
    s='ring R=0,(%s),dp; option(redSB); ideal J=%s; J=std(J); ideal I=%s; print(size(reduce(I,J))==0); quit;'%(','.join(map(str,vs)),','.join(str(g).replace('**','^') for g in Jgens),','.join(str(g).replace('**','^') for g in I))
    r=subprocess.run(['bash','-c','ulimit -v '+__import__('os').environ.get('SING_ULIM','2000000')+'; timeout '+__import__('os').environ.get('SING_TMO','3600')+' Singular -q'],input=s,capture_output=True,text=True); return r.stdout.strip()
w=sp.Symbol('w')
S=lambda *names: [sp.sympify(n) for n in names]
# chart A
vs,I=run((3,4),4)
JA=S('be12-1','be22','be11','al12','al22','al11','m1+m2+m3+1','mu2-1','mu1','y3-m3','y2-m2','y1+m2+m3+1','x3','x2','x1')
print('chart A: I contained in J:',in_ideal(vs,I,JA),flush=True)
ok=True
for g in JA:
    res=sing_unit(vs,I+[1-w*g]); ok=ok and res=='1'
    print('  g =',g,' in rad(I):',res,flush=True)
print('CHART A radical certificate:',ok,flush=True)
# chart B
vs,I=run((0,1),2)
J1=S('be22','be11','al12','al22','al11','m1','mu2-be12','mu1','y2+y3+be12+1','y1-be12','x3','x2','x1','m3*be12+y3+be12+1','m2*be12-1','y3*m2+m2+m3+1')
J2=S('be22','be11','al12','al22','al11','m2','mu2','mu1-be12','y3','y2','y1','x2+x3+be12+1','x1-be12','m3*be12+x3+be12+1','m1*be12-1','x3*m1+m1+m3+1')
print('chart B: I in J1:',in_ideal(vs,I,J1),' I in J2:',in_ideal(vs,I,J2),flush=True)
m1s,m2s=sp.symbols('m1 m2')
r0=sing_unit(vs,I+[1-w*m1s*m2s]); print('  m1*m2 in rad(I):',r0,flush=True); ok=(r0=='1')
for (Jg,extra) in ((J1,m1s),(J2,m2s)):
    for g in Jg:
        res=sing_unit(vs,I+[extra,1-w*g]); ok=ok and res=='1'
        print('  g =',g,' in rad(I + (%s)):'%extra,res,flush=True)
print('CHART B radical certificate:',ok,flush=True)
