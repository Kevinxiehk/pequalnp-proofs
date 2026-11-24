# (4,1) extensions L' = K (+) C Z over an EXPLICIT 3-dim strongly level kernel K (rows, round 12).  C^4 coordinates.
# usage: python3 -I kgen.py SPEC P K0 MODE OUT     SPEC in {A1, A2, B, Bi}; MODE cs (column sums of Z = m, sum m = 0) or cc (column-centred, Z != 0 mod K)
# Output: dim of the solution set (params, Z mod K, m); unit after saturation by prod of the other m_j  (unit <=> every such L' has a neutral column).
import sys
SPEC,P,K0,MODE,out=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4],sys.argv[5]
RV=[(2,3,5,-1),(3,-7,2,1)]          # random rows for linear gauges (family B)
pre=[]; par=[]; pareq=[]; Kdef=[]; gauge=None; rab=None; pareq_extra=[]; GC=0
if SPEC=='A1':   # x = e1 - e2, d, d' the isotropic lines of x^perp cap V (s2^2 = -2)
    par=['s2']; pareq=['s2^2+2']
    pre.append('list d=1,1,-1+s2,-1-s2; list dp=1,1,-1-s2,-1+s2; list x=1,-1,0,0;')
    Kdef=['d','-d','0','dp','dp','0','0','0','x']; gauge=[(0,0),(0,1),(0,2)]
elif SPEC=='A2': # x = (1,1,1,-3), d = zeta, d' = zetabar
    par=['om']; pareq=['om^2+om+1']
    pre.append('list d=1,om,om^2,0; list dp=1,om^2,om,0; list x=1,1,1,-3;')
    Kdef=['d','-d','0','dp','dp','0','0','0','x']; gauge=[(0,0),(0,1),(0,2)]
elif SPEC in ('B','Bi'):  # K = span{d e_a, d e_b, x e_c}, d isotropic (Walsh conic), x = d x sg(d,d) (Walsh)
    par=(['ga'] if SPEC=='B' else [])+['ii','rg']; pareq=['ii^2+1']
    dw='ga^2-1,ii*(ga^2+1),2*ga' if SPEC=='B' else '1,ii,0'
    pre.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix dW[3][1]=%s;'%dw)
    pre.append('matrix sW[3][1]=2*dW[2,1]*dW[3,1],2*dW[1,1]*dW[3,1],2*dW[1,1]*dW[2,1]; matrix xW[3][1]=dW[2,1]*sW[3,1]-dW[3,1]*sW[2,1],dW[3,1]*sW[1,1]-dW[1,1]*sW[3,1],dW[1,1]*sW[2,1]-dW[2,1]*sW[1,1];')
    pre.append('matrix dM=H*dW; matrix xM=H*xW; list d=dM[1,1],dM[2,1],dM[3,1],dM[4,1]; list x=xM[1,1],xM[2,1],xM[3,1],xM[4,1];')
    Kdef=['d','0','0','0','d','0','0','0','x']; gauge='lin'
elif SPEC in ('S+','S-','U','Ui','U2'):
    # two-column (2,1) kernels on columns a = 0, b = 1 (Walsh data).  S+/S-: the 8 isolated special points
    # ga = eps (1+sq3)(1+ii)/2, al = (-2+sq3) ga (sq3^2 = 3, ii^2 = -1), K = span{u(e_a+e_b), (p+e)e_a + (p-e)e_b, d(e_a-e_b)},
    # p = (u x rA)/(ii u.rA), e = ES (d x rB)/(ii d.rB).   U/Ui: the special line d = u: K_u = span{u e_a, p e_a, u e_b}, u on the conic (al) / at infinity.
    pre.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix rA[3][1]=2,3,5; matrix rB[3][1]=3,-7,2;')
    pre.append('proc cr(matrix a, matrix b){ matrix c[3][1]=a[2,1]*b[3,1]-a[3,1]*b[2,1],a[3,1]*b[1,1]-a[1,1]*b[3,1],a[1,1]*b[2,1]-a[2,1]*b[1,1]; return(c); }')
    pre.append('proc dt(matrix a, matrix b){ return(a[1,1]*b[1,1]+a[2,1]*b[2,1]+a[3,1]*b[3,1]); }')
    if SPEC[0]=='S':
        ES=1 if SPEC=='S+' else -1
        par=['sq3','ii','pinv','einv']; pareq=['sq3^2-3','ii^2+1']
        EPS=int(sys.argv[6]) if len(sys.argv)>6 else 1
        CJ='cj=1' in sys.argv
        pre.append('poly ga=%d*(1+sq3)*(1%sii)/2; poly al=(-2+sq3)*ga; matrix uW[3][1]=al^2-1,ii*(al^2+1),2*al; matrix dW[3][1]=ga^2-1,ii*(ga^2+1),2*ga;'%(EPS,'-' if CJ else '+'))
        pre.append('matrix pW=pinv*cr(uW,rA); matrix eW=(%d)*einv*cr(dW,rB);'%ES)
        pareq_extra=['pinv*ii*dt(uW,rA)-1','einv*ii*dt(dW,rB)-1']
        pre.append('matrix uM=H*uW; matrix dM=H*dW; matrix pM=H*pW; matrix eM=H*eW;')
        pre.append('list u,d,pe,pm; for(int ii_=1;ii_<=4;ii_++){ u[ii_]=uM[ii_,1]; d[ii_]=dM[ii_,1]; pe[ii_]=pM[ii_,1]+eM[ii_,1]; pm[ii_]=pM[ii_,1]-eM[ii_,1]; }')
        Kdef=['u','u','0','pe','pm','0','d','-d','0']
    else:
        par=(['al'] if SPEC in ('U','U2') else [])+['ii']; pareq=['ii^2+1']; pareq_extra=[]
        pre.append('matrix uW[3][1]=%s; matrix pW=cr(uW,%s);'%('al^2-1,ii*(al^2+1),2*al' if SPEC in ('U','U2') else '1,ii,0', 'rB' if SPEC=='U2' else 'rA'))
        pre.append('matrix uM=H*uW; matrix pM=H*pW; list u,pp; for(int ii_=1;ii_<=4;ii_++){ u[ii_]=uM[ii_,1]; pp[ii_]=pM[ii_,1]; }')
        Kdef=['u','0','0','pp','0','0','0','u','0']
    GC=int(sys.argv[7]) if len(sys.argv)>7 else 0
    gauge=[[(0,0),(1,0),(0,1)],[(2,0),(3,0),(2,1)],[(0,0),(2,0),(1,1)],[(1,0),(3,0),(3,1)]][GC]; par=par+['rk']
else: raise SystemExit('bad spec')
NUM=[a for a in sys.argv if a.startswith('num=')]
GNUM=[a[5:] for a in sys.argv if a.startswith('gnum=')]
if GNUM and SPEC=='B': pareq=pareq+['ga-(%s)'%GNUM[0]]
GC=(int(sys.argv[6]) if len(sys.argv)>6 else 0) if SPEC[0] not in 'SU' else GC   # gauge choice for family B (0/1: two random row pairs)
if gauge=='lin':
    r1,r2=RV[GC],RV[1-GC]
    zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if not (i==3 and j in (0,1,2))]
    # Z[3][j] (j = 0,1,2) solved from linear gauge sum_i r_i Z[i][j] = 0  (r_3 = +-1), chart r.d != 0, r'.x != 0
    zdef={}
    for j,r in ((0,r1),(1,r1),(2,r2)):
        zdef[(3,j)]='(%s)*(%s)'%(-r[3],'+'.join('%d*z%d%d'%(r[i],i,j) for i in range(3)))
    rab='rg*(%s)*(%s)-1'%('+'.join('%d*d[%d]'%(r1[i],i+1) for i in range(4)),'+'.join('%d*x[%d]'%(r2[i],i+1) for i in range(4)))
else:
    zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if (i,j) not in gauge]; zdef={g:'0' for g in gauge}
if NUM:
    v3,vi=NUM[0][4:].split(',')
    pareq=[('sq3-(%s)'%v3 if e=='sq3^2-3' else ('ii-(%s)'%vi if e=='ii^2+1' else e)) for e in pareq]
    if SPEC in ('B','Bi','U','Ui') and not GNUM: pass
mv=['m%d'%k for k in range(5) if k!=K0]
unk=par+zs+mv
MP=[a[3:] for a in sys.argv if a.startswith('mp=')]
MPS=(' minpoly=%s;'%MP[0]) if MP else ''
L=['ring R=%s,(s1,s2_,s3,t,%s),dp;%s option(redSB); LIB "elim.lib";'%(P,','.join(unk),MPS)]
L+=pre
L.append('matrix Z[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5):
        L.append('Z[%d,%d]=%s;'%(i+1,j+1,zdef.get((i,j),'z%d%d'%(i,j))))
L.append('list mm=%s;'%','.join('1' if k==K0 else 'm%d'%k for k in range(5)))
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ for(j=1;j<=5;j++){ Y[i,j]=t*Z[i,j]; } }')
cols=[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
sv=['s1','s2_','s3']
for (g,j),e in zip(cols,Kdef):
    if e=='0': continue
    if e.startswith('-'): L.append('for(i=1;i<=4;i++){ Y[i,%d]=Y[i,%d]-%s*%s[i]; }'%(j+1,j+1,sv[g],e[1:]))
    else: L.append('for(i=1;i<=4;i++){ Y[i,%d]=Y[i,%d]+%s*%s[i]; }'%(j+1,j+1,sv[g],e))
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E=%s;'%','.join(pareq))
MZ=[a[3:] for a in sys.argv if a.startswith('mz=')]
SATM=[x for x in mv if not (MZ and x[1:] in MZ[0].split(','))]
if MZ: L.append('E=E,%s;'%','.join('m%s'%k for k in MZ[0].split(',')))   # m-entries already excluded in another chart
if MODE=='cs':
    L.append('for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){cs=cs+Z[i,j];} E=E,cs-mm[j]; kill cs; }')
    L.append('E=E,1+%s;'%('+'.join(mv)))   # sum m = 0
else:
    L.append('for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){cs=cs+Z[i,j];} E=E,cs; kill cs; }')
    L.append('E=E,1+%s;'%('+'.join(mv)))   # 4x5 level: sum_j c_j(Y) = perm([J+Y;1]) - 120 = 0, so m in 1^perp
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d]; matrix T=coef(F,s1*s2_*s3*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }'%(K0+1,K0+1))
# strong-levelness self-check of K (must print 0)
L.append('matrix Y0[4][5]=subst(Y,t,0); list C0; poly chk=0; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y0[i,k]; } } } chk=chk+(perm4(M)-24)^2; kill M; }')
if gauge=='lin':
    L.append('E=E,%s;'%rab); L.append('poly dk=(%s)*(%s);'%(rab.split('*(')[1].rstrip(')'), rab.split('*(')[2].split(')')[0]))
else:
    # gauge validity: det of K's coordinates at the gauge positions
    L.append('matrix GK[3][3];')
    for g in range(3):
        for q,(i,j) in enumerate(gauge):
            L.append('GK[%d,%d]=diff(Y0[%d,%d],%s);'%(g+1,q+1,i+1,j+1,sv[g]))
    L.append('poly dk=det(GK);')
    if 'rk' in par: L.append('E=E,rk*dk-1;')
if pareq_extra:
    L.append('E=E,%s;'%','.join(pareq_extra)); L.append('poly DTU=dt(uW,rA); poly DTD=dt(dW,rB);')
L.append(('ring R2=%s,(%s),dp;'+MPS+' option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal I=std(E); poly chk=imap(R,chk); '+('poly DTU=imap(R,DTU); poly DTD=imap(R,DTD); ' if pareq_extra else '')+'ideal PE=std(ideal(%s)); chk=reduce(chk,PE);')%(P,','.join(unk),','.join(pareq+[x.replace('dt(uW,rA)','DTU').replace('dt(dW,rB)','DTD') for x in pareq_extra])))
L.append('poly dk=imap(R,dk); printf("gauge det %s",reduce(dk,PE));')
L.append('printf("K strongly level check (0 = ok): %s",chk);')
if MODE=='cc': L.append('I=std(sat(I,ideal(%s)));'%','.join(zs))
L.append('printf("KGEN %s%s mode %s chart m%d gauge %d %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); if(reduce(1,I)!=0){ ideal S=std(sat(I,ideal(%s))); printf("   after saturation by %s: dim %%s unit %%s",dim(S),(reduce(1,S)==0)); }'%(SPEC,' cj' if 'cj=1' in sys.argv else '',MODE,K0,GC,('mz='+MZ[0]) if MZ else '',P,'*'.join(SATM),'*'.join(SATM)))
if sys.argv[-1]=='comp':
    L.append('if(dim(I)>=0){ list MA=minAssGTZ(I); for(k=1;k<=size(MA);k++){ ideal Q=std(MA[k]); ideal Qm=eliminate(Q,%s); printf("  component %%s: dim %%s; m-image dim %%s; m-equations:",k,dim(Q),dim(std(Qm))); print(Qm); } }'%('*'.join(par+zs)))
    L.append('ring R3=%s,(%s),dp; ideal I=imap(R2,I);'%(P,','.join(mv+par+zs)))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
