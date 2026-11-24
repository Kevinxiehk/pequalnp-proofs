#!/bin/bash
cd "$(dirname "$0")"; : > res.log
while read c s; do n=$(echo "$c$s" | tr -d ';'); python3 -I ../b23_11.py $c "$s" 0 j_$n.sing
  r=$( (ulimit -v 500000; timeout 120 Singular -q j_$n.sing 2>&1) ); echo "$r" > j_$n.out; echo "$(echo "$r" | grep STD) $(echo "$r" | grep -c '^COMP')" >> res.log
done < jobs.txt; echo DONE >> res.log
