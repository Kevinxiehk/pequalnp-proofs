# (SM_n'') in Walsh coordinates: n vectors y_k in C^3 (columns n+1..5 zero), f = sum y_k; degree 2: y_k.(f - y_k) = 0; degree 3: per deletion
# j, sum over triples of the other nonzero columns of sg(y_a,y_b).y_c = 0 (no permanents); ISO=1 adds f.f = 0; chart f_1 = 1 (coordinate
# permutations are symmetries).  Saturation by "column k nonzero".  usage: python3 -I sm5w.py P NC ISO OUT
import sys, itertools
P,NC,ISO,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
RAB=([a[4:] for a in sys.argv if a.startswith('RAB=')] or [''])[0]
FC=int(([a[3:] for a in sys.argv if a.startswith('FC=')] or ['1'])[0])
vs=['y%d%d'%(k,c) for k in range(1,NC+1) for c in (1,2,3)]+(['zz%d'%k for k in range(1,NC+1)] if RAB else [])
L=['ring r=%s,(%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(vs))]
for k in range(1,NC+1): L.append('matrix y%d[3][1]=y%d1,y%d2,y%d3;'%(k,k,k,k))
L.append('matrix f=%s;'%'+'.join('y%d'%k for k in range(1,NC+1)))
L.append('proc dt(matrix x, matrix y){ return(x[1,1]*y[1,1]+x[2,1]*y[2,1]+x[3,1]*y[3,1]); }')
L.append('proc sg(matrix x, matrix y){ matrix s[3][1]=x[2,1]*y[3,1]+x[3,1]*y[2,1], x[1,1]*y[3,1]+x[3,1]*y[1,1], x[1,1]*y[2,1]+x[2,1]*y[1,1]; return(s); }')
L.append('ideal E=f[%d,1]-1;'%FC+(' E=E,dt(f,f);' if ISO else ''))
if RAB:
    for k in range(1,NC+1): L.append('E=E,zz%d*y%d%s-1;'%(k,k,RAB[k-1]))
for k in range(1,NC+1): L.append('E=E,dt(y%d,f-y%d);'%(k,k))
for j in range(1,6):
    terms=['dt(sg(y%d,y%d),y%d)'%T for T in itertools.combinations([k for k in range(1,NC+1) if k!=j],3)]
    if terms: L.append('E=E,%s;'%'+'.join(terms))
L.append('ideal I=std(E); printf("SMW n=%d iso=%d %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(NC,ISO,('RAB='+RAB+' FC=%d'%FC) if RAB else '',P))
for k in range(1,NC+1): L.append('if(reduce(1,I)!=0){ I=std(sat(I,ideal(y%d1,y%d2,y%d3))); printf("  after column %d nonzero: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); }'%(k,k,k,k))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
