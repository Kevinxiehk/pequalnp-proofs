# fibre-finiteness check generator: for every NONUNIT chart in LOG (systems in DIR), block order (Y-variables) > (parameters hh, tp);
# FIBRES_FINITE 1 iff every Y-variable has a pure-power leading monomial (=> coordinate ring finite over C[params] => all fibres finite)
import sys, os
log,dirn,outd=sys.argv[1:4]; os.makedirs(outd,exist_ok=True); n=0
for f in open(log).read().split('\n'):
    if 'NONUNIT' not in f: continue
    b=f.split()[0][:-3]; ms='%s/%s.ms'%(dirn,b)
    L=open(ms).read().split('\n'); v=L[0].strip().split(','); p=L[1].strip(); body=''.join(L[2:]).strip().rstrip(',')
    par=[x for x in v if x in ('hh','tp')]; yv=[x for x in v if x not in par]
    s='ring R = %s, (%s,%s), (dp(%d),dp(%d));\nideal I = %s;\nideal G = std(I);\nint ok = 1; int i; int j; int found; poly lm;\n'%(p,','.join(yv),','.join(par),len(yv),len(par),body)
    s+='for(i=1;i<=%d;i++){ found=0; for(j=1;j<=size(G);j++){ lm = leadmonom(G[j]); if (lm == var(i)^deg(lm)) { found=1; } } if(found==0){ ok=0; } }\n'%len(yv)
    s+='"FIBRES_FINITE", ok;\nquit;\n'
    open('%s/%s.sing'%(outd,b),'w').write(s); n+=1
print(n,'scripts')
