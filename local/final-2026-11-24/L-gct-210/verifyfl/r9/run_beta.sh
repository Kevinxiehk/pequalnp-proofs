#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r9
P=${1:-2147483629}
for mask in $(seq 0 31); do
  INF=""; for j in 0 1 2 3 4; do if [ $(( (mask >> j) & 1 )) -eq 1 ]; then INF="$INF$j"; fi; done
  f=m0/beta_p${P}_inf${INF:-none}.ms
  python3 -I ../exact/gen_m0a.py $P beta "$INF" $f > /dev/null
  timeout 600 msolve -g 2 -f $f -o $f.gb > /dev/null 2>&1
  n=$(grep -o "length of basis: *[0-9]*" $f.gb | grep -o "[0-9]*$"); body=$(grep -v "^#" $f.gb | tr -d ' \n')
  if [ "$body" = "[1]:" ]; then v=UNIT; elif [ -z "$n" ]; then v=FAIL; else v="NONUNIT($n)"; fi
  echo "beta INF={${INF}} p=$P: $v"
done
echo BETA_DONE
