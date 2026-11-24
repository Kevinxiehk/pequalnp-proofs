# Round 15: LEMMA S2 (exact over Q, chi-coordinates). Shape S2: Y = a (x) (1,1,1,1,-2) + b2 (x) (e_2 - e_4) + b3 (x) (e_3 - e_4), a in V,
# b2, b3 isotropic. Claim: if b2 != 0, b3 != 0 then b2 = b3.  Normalise b2 = w(t2) (scale; Y -> lam Y preserves the conditions), b3 = be w(t3)
# (both finite: the 6 special lines = orbit of the chi_3-line, pick one avoiding both b-lines).
#  mode 'neq'  : u be (t2 - t3) = 1          (b2, b3 not parallel)
#  mode 'par'  : t3 = t2, u be (be - 1) = 1  (parallel, b3 != b2)
#  mode 'cal'  : no Rabinowitsch, dim of the variety (calibration: must be non-unit, contains b2 = b3)
#  mode 'cal3' : 'neq' with only degrees 2,3 (calibration of where the contradiction comes from)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r15'); from chilib import line_eqs
mode=sys.argv[1]; K=sys.argv[2] if len(sys.argv)>2 else ''; P=sys.argv[3] if len(sys.argv)>3 else '0'
a=['a1','a2','a3']; w=lambda t,be: ['(%s)'%be,'2*(%s)*(%s)'%(be,t),'-2*(%s)*(%s)^2'%(be,t)]
b2=w('t2','1'); b3=w('t2' if mode=='par' else 't3','be')
add=lambda *v: ['('+'+'.join(x[k] for x in v)+')' for k in range(3)]
sc=lambda c,v: ['(%s)*(%s)'%(c,x) for x in v]
Y=[a,a,add(a,b2),add(a,b3),add(sc(-2,a),sc(-1,b2),sc(-1,b3))]
eqs=line_eqs(Y)
if mode=='cal3': eqs=eqs[:8]
vs=('a1,a2,a3,t2,be,u' if mode=='par' else 'a1,a2,a3,t2,t3,be,u')+(',v' if K else '')
rab={'neq':'u*be*(t2-t3)-1','cal3':'u*be*(t2-t3)-1','par':'u*be*(be-1)-1','cal':'u*be-1'}[mode]
if K: rab+=',\nv*a%s-1'%K
s='ring R=%s,(%s),dp;\noption(redSB);\nideal I=\n%s,\n%s;\nint t0=timer;\nideal G=std(I);\n"S2 %s"+"%s"+": dim",dim(G),"vdim",vdim(G),"size",size(G),"unit",(G[1]==1);\n'%(P,vs,',\n'.join(eqs),rab,mode,K)
if mode=='cal': s+='if (dim(G)>=0) { list L=minAssGTZ(I); "components:",size(L); int k; for(k=1;k<=size(L);k++){ "comp",k,"dim",dim(std(L[k])); print(L[k]); } }\n'
s+='"time",timer-t0;\nquit;\n'
open('/home/kevxhk/work/L-gct-210/stage3/r15/s2l_%s%s_%s.sing'%(mode,K,'p' if P!='0' else 'q'),'w').write(s)
print(mode,len(eqs),'equations')
