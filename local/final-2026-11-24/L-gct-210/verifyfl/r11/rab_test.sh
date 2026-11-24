#!/bin/bash
# Rabinowitsch test mod P1 for every non-unit symbolic [T22] case: final-stage GB of the non-unit S-cell + u*t*(t+1) - 1
cd /home/kevxhk/work/L-gct-210/verifyfl/r11
for C in A B; do for ci in $(grep -h "NONUNIT" n3sym_$C.log | sed 's/.*case \([0-9]*\) .*/\1/'); do
  for s in 0 1 2; do f=n3sym/sym${C}_c${ci}_s${s}_st2.ms.gb; [ -s $f ] || continue
    grep -q "length of basis: *1 element" $f && continue
    python3 -I - $f n3sym/rab_${C}${ci}_s$s.ms <<'PY'
import sys
s = open(sys.argv[1]).read(); vs = [l.split(':')[1].strip() for l in s.splitlines() if 'variable order' in l][0].split(', ')
body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; polys = [x.strip() for x in body.split(',\n') if x.strip()]
polys.append('urab*mt^2+urab*mt-1'); open(sys.argv[2], 'w').write(','.join(vs + ['urab']) + '\n2147483629\n' + ',\n'.join(polys) + '\n')
PY
    timeout 300 msolve -g 2 -f n3sym/rab_${C}${ci}_s$s.ms -o n3sym/rab_${C}${ci}_s$s.gb > /dev/null 2>&1
    echo "RAB $C case $ci scell $s: $(grep -o 'length of basis: *[0-9]*' n3sym/rab_${C}${ci}_s$s.gb)"
  done; done; done
