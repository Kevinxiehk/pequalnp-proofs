#!/bin/bash
cd "$(dirname "$0")"; : > res.log
while read c s code; do n=$(echo "$c$s$code" | tr -d ';-'); cd2=$code; [ "$code" = "-" ] && cd2=""
  python3 -I ../b23_11.py $c "$s" 0 j_$n.sing "$cd2" spec
  r=$( (ulimit -v 500000; timeout 120 Singular -q j_$n.sing 2>&1) ); echo "$r" > j_$n.out; echo "$n $(echo "$r" | grep STD | cut -d' ' -f2-) $(echo "$r" | grep -c '^COMP')" >> res.log
done < jobs.txt; echo DONE >> res.log
