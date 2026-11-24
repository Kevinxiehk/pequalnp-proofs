# Round 18: (M3) the (t2) CORE X0 = Y_ab (+) Y_cd (rows 0,1 | 2,3) of a 4x5 space: Y_ab = span((v1,w1),(v2,w2)), Y_cd = span((u1,t1),(u2,t2)).
# Charts: v1 = (1,0,*,*,*), v2 = (0,1,*,*,*) (S_5 + GL_2: the (0,1)-minor of P_a nonzero); (u1,u2) identity on the column pair UC in
# {01, 02, 23} (S_2 x S_3 representatives). Equations: all coefficients (in al,be | ga,de) of sigma_1..sigma_4 of
# x = (al v1 + be v2, al w1 + be w2, ga u1 + de u2, ga t1 + de t2).  Optional hinges (HW = 'ij' minor of (w1,w2), HT = 'kl' minor of (t1,t2)).
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
UC,P=sys.argv[1],sys.argv[2]; HW=sys.argv[3] if len(sys.argv)>3 else ''; HT=sys.argv[4] if len(sys.argv)>4 else ''
v1=['1','0','x12','x13','x14']; v2=['0','1','x22','x23','x24']
k,l=int(UC[0]),int(UC[1]); oth=[j for j in range(5) if j not in (k,l)]
u1=['0']*5; u2=['0']*5; u1[k]='1'; u2[l]='1'
for j in oth: u1[j]='y1%d'%j; u2[j]='y2%d'%j
w1=['w1%d'%j for j in range(5)]; w2=['w2%d'%j for j in range(5)]; t1=['t1%d'%j for j in range(5)]; t2=['t2%d'%j for j in range(5)]
rows=[['al*(%s)+be*(%s)'%(v1[j],v2[j]) for j in range(5)],['al*(%s)+be*(%s)'%(w1[j],w2[j]) for j in range(5)],
      ['ga*(%s)+de*(%s)'%(u1[j],u2[j]) for j in range(5)],['ga*(%s)+de*(%s)'%(t1[j],t2[j]) for j in range(5)]]
lev=[sig(rows,t,range(5)) for t in range(1,5)]
vs=['x12','x13','x14','x22','x23','x24']+[u1[j] for j in oth]+[u2[j] for j in oth]+w1+w2+t1+t2+['h1','h2']
o=['ring R0=0,(%s,al,be,ga,de),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*be*ga*de); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
if HW: i,j=int(HW[0]),int(HW[1]); o.append('C=C,h1*(w1%d*w2%d-w1%d*w2%d)-1;'%(i,j,j,i))
else: o.append('C=C,h1-1;')
if HT: i,j=int(HT[0]),int(HT[1]); o.append('C=C,h2*(t1%d*t2%d-t1%d*t2%d)-1;'%(i,j,j,i))
else: o.append('C=C,h2-1;')
o.append('ring R=%s,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,','.join(vs)))
o.append('"eqs",ncols(C); int t0=timer; ideal G=std(C); "X0 UC=%s HW=%s HT=%s: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;'%(UC,HW,HT)); o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r18/x0_%s_%s%s_%s.sing'%(UC,HW or 'n',HT or 'n','q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
