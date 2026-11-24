# (SM_n), CUBIC PART ONLY, in closed form over Q (rows, round 18).  Conic c(s) = s^2 A + s B + C (A,B,C independent), so
#   g_k = la_k c(ta_k), sum g_k = (n-2) f, f = c(sg)   <=>   sum la_k ta_k^m = (n-2) sg^m  (m = 0,1,2);
#   t(c(a),c(b),c(c)) = 16 i Phi(a,b,c),  Phi = abc(ab+bc+ca) - (a+b+c)   (rows/r13/tfac.sing), so for columns (f - g_k)/2 the cubic
#   t(y_a,y_b,y_c) is (16i/8) [Phi(s,s,s) - sum la Phi(s,s,ta) + sum la la' Phi(s,ta,ta') - la la' la'' Phi(ta,ta',ta'')].
# Conditions: per deletion j, sum over triples of the other columns (zero columns: g = f, i.e. la = 1, ta = sg).  Column k zero <=> la_k = 1,
# ta_k = sg.  The cubic part alone is a RELAXATION of (SM_n).  usage: python3 -I smphi.py P NC OUT
import sys, itertools
P,NC,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
LZ=[int(x) for x in ([a[3:] for a in sys.argv if a.startswith('LZ=')] or [''])[0].split(',') if x]   # columns with la_k = 0 (g_k = 0)
NZL='NZL' in sys.argv   # all other la_k nonzero (Rabinowitsch)
unk=['sg']+['ta%d'%k for k in range(1,NC+1) if k not in LZ]+['la%d'%k for k in range(1,NC+1) if k not in LZ]+(['rz'] if NZL else [])
L=['ring R=%s,(%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('proc Phi(poly a, poly b, poly c){ return(a*b*c*(a*b+b*c+c*a)-(a+b+c)); }')
L.append('list ta; list la; int i; int j; int k;')
for k in range(1,6):
    if k in LZ: L.append('ta[%d]=0; la[%d]=0;'%(k,k))
    elif k<=NC: L.append('ta[%d]=ta%d; la[%d]=la%d;'%(k,k,k,k))
    else: L.append('ta[%d]=sg; la[%d]=1;'%(k,k))
L.append('ideal E;')
if NZL: L.append('E=E,rz*%s-1;'%'*'.join(['la%d'%k for k in range(1,NC+1) if k not in LZ]))
for m in range(3): L.append('E=E,%s-3*sg^%d;'%('+'.join('la[%d]*ta[%d]^%d'%(k,k,m) for k in range(1,6)),m))
L.append('proc trip(int a, int b, int c){ return(Phi(sg,sg,sg)-la[a]*Phi(sg,sg,ta[a])-la[b]*Phi(sg,sg,ta[b])-la[c]*Phi(sg,sg,ta[c])+la[a]*la[b]*Phi(sg,ta[a],ta[b])+la[a]*la[c]*Phi(sg,ta[a],ta[c])+la[b]*la[c]*Phi(sg,ta[b],ta[c])-la[a]*la[b]*la[c]*Phi(ta[a],ta[b],ta[c])); }')
L.append('for(j=1;j<=5;j++){ poly F=0; int a; int b; int c; for(a=1;a<=5;a++){ for(b=a+1;b<=5;b++){ for(c=b+1;c<=5;c++){ if((a!=j)&&(b!=j)&&(c!=j)){ F=F+trip(a,b,c); } } } } E=E,F; kill F; kill a; kill b; kill c; }')
L.append('ideal I=std(E); printf("SMPHI%s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(str(NC)+(' LZ='+','.join(map(str,LZ)) if LZ else '')+(' NZL' if NZL else ''),P))
for k in [k for k in range(1,NC+1) if k not in LZ]: L.append('if(reduce(1,I)!=0){ I=std(sat(I,ideal(la%d-1,ta%d-sg))); printf("  after column %d nonzero: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); }'%(k,k,k))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
