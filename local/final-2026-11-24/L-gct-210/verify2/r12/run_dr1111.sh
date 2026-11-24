#!/bin/bash
# verify2 r12: re-run reg2's (1,1,1,1|2)(A) Omega/E_0 pipeline over Q (generator reg2/gb/gen_1111d.py, output dir mine)
cd /home/kevxhk/work/L-gct-210/verify2/r12
export OD=/home/kevxhk/work/L-gct-210/verify2/r12/dr1111
ulimit -v 2500000
for comp in g d; do for test in om e0 calom cale0; do python3 -I /home/kevxhk/work/L-gct-210/reg2/gb/gen_1111d.py $comp $test sing 0 > /dev/null 2>&1; done; done
for f in $OD/*.sing; do r=$(timeout 600 Singular -q $f 2>&1 | tr '\n' ' ' | cut -c1-40); echo "$(basename $f) :: $r"; done > dr1111.log
echo done >> dr1111.log
