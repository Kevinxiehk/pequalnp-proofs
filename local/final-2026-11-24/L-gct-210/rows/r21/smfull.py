# (SM_n) from the PERMANENTS directly (independent of the Walsh degree-2/3 formulas): columns c_k = H y_k (k = 1..NC), columns NC+1..5 zero.
# For each deletion j: coefficients of t^2, t^3, t^4 of perm(J + t M_j) vanish (t^1 is automatic for centred columns; included anyway).
# ISO=1: f.f = 0.  Chart f_1 = 1.  Options: RANK2 (all 3x3 minors of [y_1..y_NC]), PLANE (y_k3 = 0 for all k), NOP4 (drop t^4).
# Saturation by "column k nonzero".  usage: python3 -I smfull.py P NC ISO OUT [RANK2] [PLANE] [NOP4]
import sys, itertools
P,NC,ISO,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
opt=set(a for a in sys.argv[5:] if '=' not in a)
FC=int(([a[3:] for a in sys.argv[5:] if a.startswith('FC=')] or ['1'])[0])
GRAPH='GRAPH' in opt
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
vs=['y%d%d'%(k,c) for k in range(1,NC+1) for c in ((1,2) if GRAPH else (1,2,3))]+(['pp','qq'] if GRAPH else [])
def Y(k,c): return '(pp*y%d1+qq*y%d2)'%(k,k) if (GRAPH and c==3) else 'y%d%d'%(k,c)
def col(k,r):
    if k>NC: return '0'
    return '(%s)'%'+'.join('(%d)*%s'%(H[r][c],Y(k,c+1)) for c in range(3))
L=['ring r1=%s,(%s,t),dp; option(redSB); LIB "elim.lib";'%(P,','.join(vs)),'ideal E;']
for j in range(1,6):
    cs=[k for k in range(1,6) if k!=j]
    if all(k>NC for k in cs): continue
    terms=[]
    for s in itertools.permutations(range(4)):
        terms.append('*'.join('(1+t*%s)'%col(cs[r],s[r]) if cs[r]<=NC else '1' for r in range(4)))
    L.append('poly p=%s; matrix C=coeffs(p,t); int d; for(d=2;d<=nrows(C);d++){ if((d<=4) or (%d==0)){ E=E,C[d,1]; } } kill p,C,d;'%('+'.join(terms),0 if 'NOP4' in opt else 1))
L.append('ring r=%s,(%s),dp; option(redSB); ideal E=imap(r1,E);'%(P,','.join(vs)))
L.append('matrix f[3][1]=%s;'%','.join('+'.join(Y(k,c) for k in range(1,NC+1)) for c in (1,2,3)))
L.append('E=E,f[%d,1]-1;'%FC+(' E=E,f[1,1]^2+f[2,1]^2+f[3,1]^2;' if ISO else ''))
if 'PLANE' in opt: L.append('E=E,%s;'%','.join('y%d3'%k for k in range(1,NC+1)))
if 'RANK2' in opt: L.append('matrix Y[3][%d]=%s; E=E,minor(Y,3);'%(NC,','.join('y%d%d'%(k,c) for c in (1,2,3) for k in range(1,NC+1))))
tag='n=%d iso=%d %s FC=%d p=%s'%(NC,ISO,' '.join(sorted(opt)),FC,P)
L.append('ideal I=std(E); printf("SMFULL %s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%tag)
for k in range(1,NC+1): L.append('if(reduce(1,I)!=0){ I=std(sat(I,ideal(%s,%s,%s))); printf("  after column %d nonzero: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); }'%(Y(k,1),Y(k,2),Y(k,3),k))
L.append('if(reduce(1,I)!=0){ ideal F=I; write(":w %s.ideal",F); }'%out.rsplit('.',1)[0])
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
