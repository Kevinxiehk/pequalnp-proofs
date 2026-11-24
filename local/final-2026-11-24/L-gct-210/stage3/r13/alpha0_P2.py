# (alpha0), |supp W| = 2 = {0,1}: the plane P2 = {(s/2)(1,1,1,1,-2) + (c2(s)/2) n_2 (e_2 - e_4) + (c3(s)/2) n_3 (e_3 - e_4) : s in S_2} lies in K
# (S_2 = {<phi_0 - phi_1, s> = 0}, at least 2-dim; v cancels). Exact over Q(i): S_2 in Gr(2,V) charts, c2, c3 linear on S_2, n_2 = SPEC[0] (WLOG),
# n_3 in all 6 special lines.
import itertools, subprocess
def conjdot(v,w):
    m={'1':1,'I':1j,'-1':-1,'-I':-1j}; return sum((m[a].conjugate())*m[b] for a,b in zip(v,w))
SPEC=[]
for p in itertools.permutations(range(4)):
    v=[['1','I','-1','-I'][k] for k in p]
    if not any(abs(conjdot(v,w))>3.9 for w in SPEC): SPEC.append(v)
SPEC=[['(%s)'%x for x in v] for v in SPEC]
fb=[['1','-1','0','0'],['0','1','-1','0'],['0','0','1','-1']]          # basis of V
charts=[(0,1,2),(0,2,1),(1,2,0)]                                       # S_2 = span(f_a + p f_c, f_b + q f_c)
res=[]
for (ia,ib,ic) in charts:
    for k3 in range(6):
        n2=SPEC[0]; n3=SPEC[k3]
        sa=['(%s+p*(%s))'%(fb[ia][r],fb[ic][r]) for r in range(4)]; sb=['(%s+q*(%s))'%(fb[ib][r],fb[ic][r]) for r in range(4)]
        s=['(x*%s+y*%s)'%(sa[r],sb[r]) for r in range(4)]; c2='(x*ga+y*gb)'; c3='(x*da+y*db)'
        out=['ring R=(0,I),(p,q,ga,gb,da,db,t,x,y),dp;','minpoly=I^2+1;','matrix Y[4][5];']
        for r in range(4):
            out.append('Y[%d,1]=%s/2; Y[%d,2]=%s/2;'%(r+1,s[r],r+1,s[r]))
            out.append('Y[%d,3]=(%s+%s*%s)/2; Y[%d,4]=(%s+%s*%s)/2;'%(r+1,s[r],c2,n2[r],r+1,s[r],c3,n3[r]))
            out.append('Y[%d,5]=-%s-(%s*%s+%s*%s)/2;'%(r+1,s[r],c2,n2[r],c3,n3[r]))
        perms=list(itertools.permutations(range(4)))
        for jd in range(5):
            cols=[c for c in range(5) if c!=jd]
            out.append('poly C%d='%jd+'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[pp[r]]+1) for r in range(4)) for pp in perms)+';')
        out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal J; int k; int j; matrix M;')
        out.append('for(k=1;k<=4;k++){ M=coef(D[k],t*x*y); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} } J=simplify(J,2);')
        out.append('ring R2=(0,I),(p,q,ga,gb,da,db),dp; minpoly=I^2+1; ideal J=imap(R,J); ideal G=std(J); "RESULT P2 chart %d%d%d n3=%d size",size(G),"dim",dim(G);'%(ia,ib,ic,k3))
        out.append('quit;')
        fn='/home/kevxhk/work/L-gct-210/stage3/r13/a0P2_%d%d%d_%d.sing'%(ia,ib,ic,k3); open(fn,'w').write('\n'.join(out)+'\n')
        r=subprocess.run(['/usr/bin/Singular','-q',fn],capture_output=True,text=True,timeout=600).stdout
        line=[l for l in r.splitlines() if l.startswith('RESULT')]; res.append(line[0] if line else 'ERROR '+r[-200:]); print(res[-1],flush=True)
print('P2 systems',len(res),'unit',sum(1 for l in res if 'size 1 dim -1' in l),flush=True)
