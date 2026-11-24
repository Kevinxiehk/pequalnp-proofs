# REAL post-processor (R21.7) for Walsh-coordinate .sing files over Q(i) (ring variable ii, generator ii^2+1).
# Every vector in these generators is D * (rational vector), D = diag(1, ii, 1) (conic cc, cd: second coordinate carries the ii).  The
# symmetry x_2 -> -x_2 (H -> -(row permutation of H)) makes every condition (power of i) x (rational polynomial).  realsplit(J): reduce
# each generator mod ii^2+1 to g0 + ii*g1; if g0*g1 == 0 keep the nonzero part (exactly equivalent over C); otherwise print
# "REALSPLIT PARITY FAILURE" and keep g together with ii^2+1 (so the run stays correct, just not ii-free).  Optional SUB=v1,v2,..: first
# substitute v -> ii*v (an invertible change of variables over C) for free second coordinates.  Patched calls: std(E), std(EP), and the
# saturation ideals sat(I, X) -> sat(I, realsplit(X)).  ii stays a (now unused) ring variable: dimensions are +1, unit verdicts unchanged.
# usage: python3 -I realify.py IN OUT [SUB=...]
import sys, re
src,out=sys.argv[1],sys.argv[2]
SUB=([a[4:] for a in sys.argv[3:] if a.startswith('SUB=')] or [''])[0]
s=open(src).read()
assert 'ii^2+1' in s, 'not a Q(i) file'
subs=''.join('J=subst(J,%s,ii*%s); '%(v,v) for v in SUB.split(',') if v)
proc=('proc realsplit(ideal J){ %sideal SI=std(ideal(ii^2+1)); ideal O; int q; int bad=0; poly g; poly g0; poly g1; '
      'for(q=1;q<=ncols(J);q++){ g=reduce(J[q],SI); g0=subst(g,ii,0); g1=subst(diff(g,ii),ii,0); '
      'if((g0!=0) and (g1!=0)){ bad++; O=O,g; } else { if(g0!=0){ O=O,g0; } else { if(g1!=0){ O=O,g1; } } } } '
      'if(bad>0){ print("REALSPLIT PARITY FAILURE: "+string(bad)); O=O,ii^2+1; } else { print("realsplit ok: "+string(ncols(J))+" generators"); } return(O); }'%subs)
lines=s.split('\n')
lines.insert(1,proc)
s='\n'.join(lines)
n0=s.count('std(E)')+s.count('std(EP)')
s=s.replace('std(E)','std(realsplit(E))').replace('std(EP)','std(realsplit(EP))')
s,nsat=re.subn(r'sat\((\w+),([^()]*(?:\([^()]*\))?[^()]*)\)',lambda m:'sat(%s,realsplit(%s))'%(m.group(1),m.group(2)),s)
open(out,'w').write(s)
print('written',out,'| std patched:',n0,'| sat patched:',nsat)
