# Round 13: (alpha0) with |supp W| = 3 or 2 after the shape-S / S-SPEC reduction. Singular-native exact systems over Q(i).
# usage: python3 -I alpha0_small.py MODE   MODE = s3 (|supp| = 3: v, n_3 special, 36 combos) | s2 (|supp| = 2: v = w(tau) or chi_3, n_2, n_3 special)
import itertools, subprocess, sys, re
MODE=sys.argv[1]
def conjdot(v,w):
    m={'1':1,'I':1j,'-1':-1,'-I':-1j}; return sum((m[a].conjugate())*m[b] for a,b in zip(v,w))
SPEC=[]
for p in itertools.permutations(range(4)):
    v=[['1','I','-1','-I'][k] for k in p]
    if not any(abs(conjdot(v,w))>3.9 for w in SPEC): SPEC.append(v)
SPEC=[['(%s)'%x for x in v] for v in SPEC]
Sv=['s1','(s2-s1)','(s3-s2)','(-s3)']
def system(Zcols,ncols,supp,extra_vars,extra_eqs,tag):
    """Zcols[j]: 4 entry strings of column j of Z (j = 0..3; column 4 of Z is 0); ncols[j]: direction n_j for j not in supp (strings)."""
    fv=['f%d_%d'%(k,i) for k in range(4) for i in range(3)]
    j0=min(supp); fvars=[x for x in fv if not x.startswith('f%d_'%j0)]
    F={}
    for k in range(4):
        F[k]=['0']*4 if k==j0 else ['f%d_0'%k,'f%d_1'%k,'f%d_2'%k,'(-(f%d_0+f%d_1+f%d_2))'%(k,k,k)]
    cc={j:'('+'+'.join('%s*%s'%(F[j][r],Sv[r]) for r in range(4))+')' for j in range(4)}
    N={j:(Zcols[j] if j in supp else ncols[j]) for j in range(4)}
    out=['ring R=(0,I),(%s,t,s1,s2,s3,mu),dp;'%','.join(fvars+extra_vars),'minpoly=I^2+1;','matrix Y[4][5];']
    for r in range(4):
        for j in range(4):
            zj=Zcols[j][r] if j in supp else '0'
            out.append('Y[%d,%d]=(%s+%s*%s)/2+mu*%s;'%(r+1,j+1,Sv[r],cc[j],N[j][r],zj))
        out.append('Y[%d,5]=-%s-('%(r+1,Sv[r])+'+'.join('%s*%s'%(cc[j],N[j][r]) for j in range(4))+')/2;')
    perms=list(itertools.permutations(range(4)))
    for jd in range(5):
        cols=[x for x in range(5) if x!=jd]
        out.append('poly C%d='%jd+'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in perms)+';')
    out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal J; int k; int j; matrix M;')
    out.append('for(k=1;k<=4;k++){ M=coef(D[k],t*s1*s2*s3*mu); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} }')
    out.append('J=J,%s; J=simplify(J,2);'%(','.join(extra_eqs) if extra_eqs else '0'))
    out.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal J=imap(R,J); ideal G=std(J); "RESULT %s size",size(G),"dim",dim(G);'%(','.join(fvars+extra_vars),tag))
    out.append('quit;')
    fn='/home/kevxhk/work/L-gct-210/stage3/r13/a0small_%s.sing'%tag; open(fn,'w').write('\n'.join(out)+'\n')
    res=subprocess.run(['/usr/bin/Singular','-q',fn],capture_output=True,text=True,timeout=300).stdout
    line=[l for l in res.splitlines() if l.startswith('RESULT')]; return line[0] if line else 'ERROR '+res[-300:]
results=[]
if MODE=='s3':
    for iv,inn in itertools.product(range(6),range(6)):
        v=SPEC[iv]; l=['1','l1','(-1-l1)']
        Z={j:['(%s)*%s'%(l[j],v[r]) for r in range(4)] for j in range(3)}; Z[3]=['0']*4
        r=system(Z,{3:SPEC[inn]},{0,1,2},['l1','q'],['q*l1*(1+l1)-1'],'s3_v%d_n%d'%(iv,inn)); results.append(r); print(r,flush=True)
else:
    w=['(1+2*tau+(-2)*tau^2)','(I+2*tau*(-1)+(-2)*tau^2*(-I))','(-1+2*tau+(-2)*tau^2*(-1))','(-I+2*tau*(-1)+(-2)*tau^2*(I))']  # chi_1 + 2 tau chi_2 - 2 tau^2 chi_3
    chi3=['(1)','(-I)','(-1)','(I)']
    for vname,vv,ev in (('tau',w,['tau']),('chi3',chi3,[])):
        for i2,i3 in itertools.product(range(6),range(6)):
            Z={0:vv,1:['(-%s)'%x for x in vv],2:['0']*4,3:['0']*4}
            r=system(Z,{2:SPEC[i2],3:SPEC[i3]},{0,1},ev,[],'s2_%s_n%d_n%d'%(vname,i2,i3)); results.append(r); print(r,flush=True)
nu=sum(1 for r in results if 'size 1 dim -1' in r); print('MODE',MODE,': systems',len(results),' unit',nu,' other',len(results)-nu,flush=True)
