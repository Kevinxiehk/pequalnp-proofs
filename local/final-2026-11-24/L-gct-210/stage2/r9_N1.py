# Necessary condition (N1) [NOTES-stage2 R9-8] for (0,e_m) in Omega, Case B with b = 0 on X (lam = 0), non-PROP:
#   on X_s := X cap {s_1 = s_2 = 0} (where s = 0, q_0 = 0, p_0 = -a, b = 0) there is T in C^4 with
#      (A)  2 p_m q_m - 2 a q_m - a Q_T = 0      and      (B)  p_m q_m + sum_j T_j p_j q_j = 0      (identities of quadrics on X_s).
# D0-4 families: X_s = lift( span(w1, w2, F3*h - F0*y3) ), (F0,F3) = (f0,f3) in case (i) or (d0,d3) in case (ii) -- the same system.
# usage: r9_N1.py PAT CHO CHAR  -> Singular script (m = 1,2,3; unknowns T^(m)), prints the parameter locus (elimination of the T's).
import sys
pat,cho,ch=sys.argv[1],sys.argv[2],sys.argv[3]
Z4=['0']*4
if pat in ('Q0','P0'):
    par=['r1','r2']; V=[['1','0','r1','(-1-r1)'],['0','1','r2','(-1-r2)']]
    w=['(-r1*(3+r1+r2)+(1+r1)*(r1+r2-1))','(-r2*(3+r1+r2)+(1+r2)*(r1+r2-1))','(3+r1+r2)','(r1+r2-1)']
    e34=['0','0','1','-1']
    if pat=='Q0': Wb=[(V[0],Z4),(V[1],Z4)]; y3=(e34,Z4) if cho=='A' else (Z4,w)
    else:         Wb=[(Z4,V[0]),(Z4,V[1])]; y3=(Z4,e34) if cho=='A' else (w,Z4)
else:
    par=[]; Wb=[(['1','-1','0','0'],Z4),(Z4,['0','0','1','-1'])]
    y3=(['-1','-1','1','1'],Z4) if cho=='A' else (Z4,['1','1','-1','-1'])
par+=['F0','F3']
h=(['1']*4,Z4)
v3=(['(F3*1-F0*(%s))'%y3[0][j] for j in range(4)],['(-F0*(%s))'%y3[1][j] for j in range(4)])
basis=[Wb[0],Wb[1],v3]
unk=['T%d_%d'%(m,j) for m in (1,2,3) for j in range(1,5)]
print('ring R=%s,(%s),dp;'%(ch,','.join(unk+par+['z1','z2','z3'])))
for j in range(4):
    print('poly p%d=%s; poly q%d=%s;'%(j+1,'+'.join('z%d*(%s)'%(k+1,basis[k][0][j]) for k in range(3)),j+1,'+'.join('z%d*(%s)'%(k+1,basis[k][1][j]) for k in range(3))))
print('poly a=p1+p2+p3+p4; poly b=q1+q2+q3+q4; ideal I; matrix C; int k; poly F;')
print('"b must vanish on X_s:", b==0;')
for m in (1,2,3):
    QT='+'.join('T%d_%d*q%d'%(m,j,j) for j in range(1,5)); PQ='+'.join('T%d_%d*p%d*q%d'%(m,j,j,j) for j in range(1,5))
    for F in ('2*p%d*q%d-2*a*q%d-a*(%s)'%(m,m,m,QT), 'p%d*q%d+%s'%(m,m,PQ)):
        print('F=%s; C=coef(F,z1*z2*z3); for(k=1;k<=ncols(C);k++){I=I+ideal(C[2,k]);}'%F)
print('int t=timer; poly tt=1; int ii; for(ii=1;ii<=12;ii++){tt=tt*var(ii);} ideal E=std(eliminate(I,tt));')
print('"N1 %s_%s char %s: ELIM"; E; LIB "primdec.lib"; "PRIMES"; minAssGTZ(E); "sec",timer-t;'%(pat,cho,ch))
print('quit;')
