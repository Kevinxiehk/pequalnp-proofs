# Pattern (2,1,1|2) case (ii), version 2 of gen_dr211c.py: the Omega-test with X NORMALISED modulo M + C d_0
# (valid: row 0 is deletable, so d_0 = (e_0 - 1/4) (x) 1 lies in E_0 by Lemma DL; the pivot matrix of {d_0, B_1..B_6} at
#  x34, x00, x0ja, x10, x20, x1jb, x2jc has determinant -a_ja * b_jb * c_jc / 4 (up to sign) != 0 on the chart).
# Writes msolve inputs (elimination of z, x, r: '-e k') or Singular scripts (std or eliminate) for each chart.
#   usage: gen_dr211d.py COMP(g|d) TEST(om|calom|e0|cale0) ENGINE(ms|sing|singel) CHAR
import sys, os; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
comp,test,engine,char=sys.argv[1],sys.argv[2],sys.argv[3],int(sys.argv[4])
od=os.environ.get('OD','/tmp/dr211d'); os.makedirs(od,exist_ok=True)
exec(open('/home/kevxhk/work/L-gct-210/reg2/gb/dr211_common.py').read())
def emit(tag,polys,elimvars):
    names=F.names
    if engine=='ms':
        # variable order: elimination block first
        order=elimvars+[v for v in names if v not in elimvars]
        perm_=[names.index(v) for v in order]
        lines=[]
        for q in polys:
            qq={tuple(k[i] for i in perm_):v for k,v in q.items()}
            s=to_str(qq,order,char)
            if s!='0': lines.append(s)
        open('%s/%s.ms'%(od,tag),'w').write(','.join(order)+'\n%d\n'%char+',\n'.join(lines)+'\n')
        open('%s/%s.nelim'%(od,tag),'w').write('%d\n'%len(elimvars))
    else:
        lines=[to_str_Q(q,names) for q in polys]; lines=[l for l in lines if l!='0']
        if engine=='sing': body='ideal G=std(I);\nprint(size(G));\nprint(G[1]);'
        else: body='ideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);\nprint("FACTORS");\nint i; for(i=1;i<=size(J);i++){print(factorize(J[i]));}'%('*'.join(elimvars))
        open('%s/%s.sing'%(od,tag),'w').write('ring R=%d,(%s),dp;\noption(redSB);\nideal I=%s;\n%s\nquit;\n'%(char,','.join(names),',\n'.join(lines),body))
cnt=0
for (jc,ja,base,zero) in charts():
    elimv=['z']+F.xv+F.rv
    s=W('r1')
    for j in range(2,5): s=add(s,W('r%d'%j))
    if test=='om':
        for jr in range(1,5):
            emit('%s_om_c%s_a%d_r%d'%(comp,jc,ja+1,jr),base+F.fo+[W(v) for v in zero]+[W('r0'),s,F.eq('r%d'%jr,1)],elimv); cnt+=1
    elif test=='calom':
        emit('%s_calom_c%s_a%d'%(comp,jc,ja+1),base+F.fo+[W(v) for v in zero]+[F.eq('r0',1)]+[W('r%d'%j) for j in range(1,5)],elimv); cnt+=1
    elif test=='e0':
        for xn in [v for v in F.xv if v not in zero]:
            emit('%s_e0_c%s_a%d_%s'%(comp,jc,ja+1,xn),base+F.fo+[W(r) for r in F.rv]+[W(v) for v in zero]+[F.eq(xn,1)],elimv); cnt+=1
    elif test=='cale0':
        emit('%s_cale0_c%s_a%d'%(comp,jc,ja+1),base+F.fo+[W(r) for r in F.rv]+[W(v) for v in zero if v!='x34']+[F.eq('x34',1)],elimv); cnt+=1
print('wrote %d files to %s'%(cnt,od))
