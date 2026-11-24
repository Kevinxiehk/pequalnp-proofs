# Pattern (2,1,1|2), incidence case (ii): V = {x : x_0 = 0, sum x = 0} (column 0, rows 1,2,3); rows 1, 2 carry e_1 (0,b)^T, e_2 (0,c)^T with
#   b, c in H (sum-zero on columns 1..4), <b,c> = 0;  row 0 carries U_0 = span(5 e_0 - 1, (0,a)), a in H, <a,b> = <a,c> = 0.
# parameter charts as in gen_nc.py.   modes: lev | cal | om | e0
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
import subprocess
p=int(sys.argv[1]); mode=sys.argv[2]
av=['a%d'%i for i in range(1,5)]; bv=['b%d'%i for i in range(1,5)]; cv=['c%d'%i for i in range(1,5)]
def basis(R,V):
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    B1=Z(); B1[0][0]=c(4)
    for j in range(1,5): B1[0][j]=c(-1)
    B2=Z(); B3=Z(); B4=Z()
    for j in range(4): B2[0][1+j]=V(av[j]); B3[1][1+j]=V(bv[j]); B4[2][1+j]=V(cv[j])
    B5=Z(); B5[1][0]=c(1); B5[2][0]=c(-1)
    B6=Z(); B6[2][0]=c(1); B6[3][0]=c(-1)
    return [B1,B2,B3,B4,B5,B6]
F=Family(av+bv+cv,basis,6); W=F.W
def dot(u,v):
    q={}
    for s,t in zip(u,v): q=add(q,mul(W(s),W(t)))
    return q
def sm(u):
    q={}
    for s in u: q=add(q,W(s))
    return q
fam=[sm(av),sm(bv),sm(cv),dot(av,bv),dot(av,cv),dot(bv,cv)]
print('level equations %d, FO equations %d'%(len(F.level),len(F.fo)),flush=True)
def sing(polys,elim=None,extra=''):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    body='ideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);'%elim if elim else 'ideal J=std(I);\nprint(size(J));print(J[1]);'
    script='ring R=%d,(%s),dp;\noption(redSB);\nideal I=%s;\n%s\n%s\nquit;\n'%(p,','.join(F.names),',\n'.join(lines),body,extra)
    open('/tmp/s211b.sing','w').write(script)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/s211b.sing'),capture_output=True,text=True,timeout=140)
    return ' '.join(r.stdout.split())
charts=[(1,1,1),(1,1,2),(1,2,1),(1,2,2),(1,2,3)]
if mode=='lev':
    # level ideal modulo the P_2 relations: is anything else needed ?
    names=av+bv+cv
    lines=[to_str_Q({k[:12]:v for k,v in q.items()},names) for q in F.level]
    fl=[to_str_Q({k[:12]:v for k,v in q.items()},names) for q in fam]
    script='ring R=%d,(%s),dp;\noption(redSB);\nideal Fam=%s;\nFam=std(Fam);\nideal Lv=%s;\nprint("level generators not in the P_2 ideal:");\nint i; for(i=1;i<=size(Lv);i++){ if(reduce(Lv[i],Fam)!=0){print(reduce(Lv[i],Fam));} }\nprint("done");quit;\n'%(p,','.join(names),',\n'.join(fl),',\n'.join(l for l in lines if l!='0'))
    open('/tmp/s211b.sing','w').write(script)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/s211b.sing'),capture_output=True,text=True,timeout=140); print(r.stdout[:1500])
else:
    allunit=True
    for (ja,jb,jc) in charts:
        par=[F.eq('a%d'%ja,1),F.eq('b%d'%jb,1),F.eq('c%d'%jc,1)]
        if mode=='cal':
            print('chart %s CAL rho=e_0:'%str((ja,jb,jc)),sing(F.level+F.fo+fam+par+[F.eq('r0',1)]+[W('r%d'%j) for j in range(1,5)])[:40]); continue
        if mode=='om':
            for jr in range(1,5):
                s=W('r1')
                for j in range(2,5): s=add(s,W('r%d'%j))
                out=sing(F.level+F.fo+fam+par+[s,F.eq('r%d'%jr,1)]); u=(out=='1 1'); allunit=allunit and u
                print('chart %s rho_%d=1: %s'%(str((ja,jb,jc)),jr,'UNIT' if u else out[:80]),flush=True)
    print('ALL UNIT' if allunit and mode=='om' else '')
