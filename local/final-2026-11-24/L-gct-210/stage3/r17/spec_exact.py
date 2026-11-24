# Round 17: (PR3) stratum (II), SPECIAL LOCUS h_0 = s e_0 (s = 1, WLOG by row/column symmetry), exact over Q (or P1 with P).
#   h_1 = (1, y1..y4), h_2 = (1, z1..z4), sum y = sum z = 0; Delta = span((0,y), (0,z)), chart u (y1 z2 - y2 z1) = 1 (S_4 on columns 1..4);
#   x* = (r_0, r_1, -r_0-r_1), chart r_{I,J} = 1.  Equations: all (a,b,d)-coefficients of sigma_1..3 of x = (a h_0, b h_1, (-a-b) h_2) + d x*, and
#   Delta-membership of c, D_2, D_3: entry 0 = 0 and det[y, z, v]_{rows 1,2,k} = 0 (k = 3,4).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
I,J,P=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; alg=sys.argv[4] if len(sys.argv)>4 else 'slimgb'
y=['(-y2-y3-y4)','y2','y3','y4']; z=['(-z2-z3-z4)','z2','z3','z4']   # y1 = -(y2+y3+y4)
h0=['1','0','0','0','0']; h1=['1']+y; h2=['1']+z; H=[h0,h1,h2]
r0=['r0_%d'%j for j in range(5)]; r1=['r1_%d'%j for j in range(5)]
(r0 if I==0 else r1)[J]='1'
r2=['(-(%s)-(%s))'%(r0[j],r1[j]) for j in range(5)]; R=[r0,r1,r2]
co=['a','b','(-a-b)']
rows=[['(%s)*%s+d*%s'%(co[i],H[i][j],R[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=['y2','y3','y4','z2','z3','z4']+[x for x in r0+r1 if x!='1']+['u']
o=['ring R0=0,(%s,a,b,d),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int l; matrix M; poly g;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*d); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }']
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    o.append('M=coef(%s_0,a*b*d); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; }'%nm)
    for k in (3,4):
        o.append('g=det(matrix(ideal(%s,%s,%s_1, %s,%s,%s_2, %s,%s,%s_%d),3,3)); M=coef(g,a*b*d); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; }'%(
            y[0],z[0],nm, y[1],z[1],nm, y[k-1],z[k-1],nm,k))
o.append('C=C,u*((%s)*(%s)-(%s)*(%s))-1;'%(y[0],z[1],y[1],z[0]))
o.append('ring R=%s,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,','.join(vs)))
o.append('"eqs",ncols(C); int t0=timer; ideal G=%s(C);'%alg)
o.append('"SPEC %d%d: dim",dim(std(G)),"unit",(G[1]==1),"time",timer-t0;'%(I,J)); o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r17/spec_%d%d_%s.sing'%(I,J,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
