# char-0 Jacobian rank of the K' chart system at the known (rational!) points: the k3gen equations have INTEGER coefficients
# (isotropic formulas), and the known points have coordinates in {0, +-1}.  Uses the char-p system file only for the polynomial
# STRUCTURE -- so regenerate equations over Q with Singular char 0 instead.  usage: python3 -I k3jac0.py S J
import sys, subprocess, itertools, sympy as sp
S=sys.argv[1]; J=int(sys.argv[2]); n=S.replace(',','_')
# build a char-0 version of the system: same generator with P = 0
subprocess.run(['python3','-I','k3gen.py','0',S,str(J),'kq/k_%s_J%d.ms'%(n,J)],check=True)
sing=open('kq/k_%s_J%d.sing'%(n,J)).read().replace('ring R = 0,','ring R = 0,')
open('kq/k_%s_J%d.sing'%(n,J),'w').write(sing)
subprocess.run(['Singular','-q','kq/k_%s_J%d.sing'%(n,J)],check=True,stdout=subprocess.DEVNULL)
L=open('kq/k_%s_J%d.ms'%(n,J)).read().split('\n'); vars_=L[0].split(','); eqs=[e for e in ''.join(L[2:]).split(',') if e.strip()]
syms=sp.symbols(vars_); env=dict(zip(vars_,syms))
E=[sp.sympify(e.replace('^','**'),locals=env) for e in eqs]
Jm=sp.Matrix([[sp.diff(e,x) for x in syms] for e in E])
Sv=[int(c) for c in S.split(',')]
cnt=0
for p,q in itertools.combinations(range(5),2):
    rest=[j for j in range(5) if j not in (p,q)]
    for s1,s2 in itertools.combinations(rest,2):
        for mir in (0,1):
            a=[0]*10; a[(5 if mir else 0)+p]=1; a[(5 if mir else 0)+q]=-1
            b1=[0]*10; b1[(0 if mir else 5)+s1]=1; b2=[0]*10; b2[(0 if mir else 5)+s2]=1
            m=[0]*5; m[p]=1; m[q]=-1
            M=sp.Matrix([a,b1,b2]); sub=M[:,Sv]
            if sub.det()==0 or m[J]==0: continue
            G=sub.inv()*M; val={}
            free=[c for c in range(10) if c not in Sv]
            for s in range(3):
                for c in free: val['g%d_%d'%(s,c)]=G[s,c]
            for j in range(5):
                if j!=J: val['M%d'%j]=sp.Rational(m[j],m[J])
            subs={env[v]:val[v] for v in vars_}
            res=[e.subs(subs) for e in E]; nz=sum(1 for r in res if r!=0)
            rk=Jm.subs(subs).rank()
            cnt+=1; print((p,q,s1,s2,mir),'nonvanishing',nz,'char-0 Jacobian rank',rk,'of',len(vars_),flush=True)
print('chart',S,'J',J,'known points',cnt)
