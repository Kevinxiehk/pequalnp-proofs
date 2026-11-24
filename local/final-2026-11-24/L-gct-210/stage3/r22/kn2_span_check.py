# exact level check (over Q(w)) of the forced spans: M1 -> 4 single-row + free column (col 4, rows 0,1,3,4); M0 -> 4 single-row + (r2-r4) (x) mbar
# + (r0-r4) (x) e4 + (r1-r4) (x) e4. Elements as 5x5 string matrices (row index = matrix row).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
which=sys.argv[1]
def srow(i,v):
    M=[['0']*5 for _ in range(5)]; M[i]=list(v); return M
def colel(c,j):
    M=[['0']*5 for _ in range(5)]
    for i,ci in enumerate(c): M[i][j]=ci
    return M
def rank1(c,v):
    return [['(%s)*(%s)'%(ci,vj) for vj in v] for ci in c]
m=['1','w^2','w','0','0']; mb=['1','w','w^2','0','0']
if which=='M1':
    E=[srow(0,m),srow(1,m),srow(2,['1','1','1','1','-4']),srow(3,['1','1','1','-3','0']),
       colel(['1','0','0','0','-1'],4),colel(['0','1','0','0','-1'],4),colel(['0','0','0','1','-1'],4)]
else:
    E=[srow(0,m),srow(1,m),srow(2,['0','0','0','1','-1']),srow(3,['2','2','2','-3','-3']),
       rank1(['0','0','1','0','-1'],mb),colel(['1','0','0','0','-1'],4),colel(['0','1','0','0','-1'],4)]
cs=['c%d'%i for i in range(len(E))]
rows=[['+'.join('%s*(%s)'%(cs[a],E[a][i][j]) for a in range(len(E))) for j in range(5)] for i in range(5)]
lev=[sig(rows,s,range(5)) for s in range(1,6)]
o=['ring R=(0,w),(%s),dp; minpoly=w^2+w+1;'%','.join(cs),'ideal L=%s;'%','.join(lev),'L=simplify(L,2); "%s span level (all sigma_t identically 0):",size(L)==0; if(size(L)>0){L;}'%which,'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r22/span_%s.sing'%which; open(f,'w').write('\n'.join(o)+'\n'); print(f)
