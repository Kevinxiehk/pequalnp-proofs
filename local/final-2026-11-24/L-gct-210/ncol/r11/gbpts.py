# list the points of a 0-dim restricted-K0 GB (from k0r.py): minimal primes in lex order, with u (a-vector), p (b-vector), m.
# usage: python3 -I gbpts.py JOB.sing JOB.gb OUT.sing
import sys,re
s=open(sys.argv[1]).read(); gb=open(sys.argv[2]).read().strip().rstrip(',')
m=re.search(r'ring R2 = (\S+), \(([^)]*)\), dp;',s); ch,unk=m.group(1),m.group(2)
L=['LIB "primdec.lib";','ring S = %s, (%s), dp;'%(ch,unk),'ideal G = %s;'%gb,'list pr = minAssGTZ(G); "NPRIMES", size(pr);',
 'ring Sl = %s, (%s), lp;'%(ch,unk),'list pr = imap(S, pr); int i;',
 'for(i=1;i<=size(pr);i++){ ideal P = std(pr[i]); "PRIME", i, "vdim", vdim(P); P; kill P; }','quit;']
open(sys.argv[3],'w').write('\n'.join(L)+'\n')
