# verify2 r24: (SM5) restricted to the coordinate plane x3 = 0 (Walsh), the mechanism of the SM4 counterexample. f = (1,i,0) WLOG (isotropic in the plane:
# f ~ (1,+-i,0); the conjugate case is the image under x2 -> -x2, a symmetry of the plane problem); g_k = f - 2 y_k isotropic in the plane: g_k = al_k (1,i,0) or
# be_k (1,-i,0); sum g_k = 3 f (5 columns). Degree 3 is automatic (kappa = 0 on the plane); impose sigma_4 (permanent) of every 4x4 deletion; all columns nonzero.
import itertools, subprocess
H='matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;'
out=[]
for types in itertools.product('ab',repeat=4):
    if types>tuple(sorted(types)): continue   # columns are symmetric: only the number of b-columns matters
    nb=types.count('b'); na=4-nb
    vs=['x%d'%k for k in range(4)]
    L=['ring R=(0,i),(%s),dp; minpoly=i^2+1; LIB "elim.lib";'%','.join(vs),H,'matrix f[3][1]=1,i,0; matrix pa[3][1]=1,i,0; matrix pb[3][1]=1,-i,0;']
    for k,tp in enumerate(types): L.append('matrix g%d=x%d*p%s; matrix y%d=H*((f-g%d)/2);'%(k,k,tp,k,k))
    sa='+'.join('x%d'%k for k,tp in enumerate(types) if tp=='a') or '0'; sb='+'.join('x%d'%k for k,tp in enumerate(types) if tp=='b') or '0'
    L.append('matrix y4[4][1]; ideal E=(%s)-2,%s;'%(sa,sb))
    L.append('matrix Y[4][5]; int r; int k; int j; for(r=1;r<=4;r++){ Y[r,1]=y0[r,1]; Y[r,2]=y1[r,1]; Y[r,3]=y2[r,1]; Y[r,4]=y3[r,1]; Y[r,5]=y4[r,1]; }')
    L.append('proc perm4(matrix M){ poly q=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; q=q+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; } } } } } return(q); }')
    L.append('for(j=1;j<=5;j++){ matrix M[4][4]; int c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(r=1;r<=4;r++){ M[r,c]=Y[r,k]; } } } E=E,perm4(M); kill M; kill c; }')
    L.append('ideal G=std(E);')
    for k in range(4): L.append('G=std(sat(G,ideal(y%d[1,1],y%d[2,1],y%d[3,1],y%d[4,1])));'%(k,k,k,k))
    L.append('printf("CALIBRATION n=4, plane x3=0, %d a-columns / %d b-columns: dim %%s unit %%s",dim(G),reduce(1,G)==0); quit;'%(na,nb))
    fn='plane4_%d.sing'%nb; open(fn,'w').write('\n'.join(L)+'\n')
    r=subprocess.run('ulimit -v 1500000; timeout 600 Singular -q '+fn,shell=True,capture_output=True,text=True)
    out.append(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else 'FAILED '+r.stderr[-100:])
    print(out[-1],flush=True)
