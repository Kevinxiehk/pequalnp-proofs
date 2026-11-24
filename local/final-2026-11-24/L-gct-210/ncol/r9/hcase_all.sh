#!/bin/sh
# hcase_all.sh TC : all six closed case systems (COLL01, COLL02, COLL12, E1, E2, E3; NOTES R9.3) on the 74 orbit-representative charts
# of type a3, family TC, with the RSS-capped runner.  Env: ULIM (virtual KB), RSSKB (resident cap), CT (seconds).
cd "$(dirname "$0")"
tc=$1; od=hcase_T$tc; mkdir -p $od
for S in $(awk '{print $1}' ../r8/repsh.txt); do n=$(echo $S|tr , _)
  for c in E3 CA01_0 CA01_1 CA02_0 CA02_1 CA12_0 CA12_1 CB01_0 CB01_1 CB02_0 CB02_1 CB12_0 CB12_1; do f=$od/h_${n}_T${tc}_$c.ms; [ -f $f ] && continue
    python3 -I ../r8/hgenc.py 65521 $S $tc $f $c >/dev/null && (ulimit -v 2000000; timeout 120 Singular -q ${f%.ms}.sing >/dev/null 2>&1); done; done
../gb/runlog_rss.sh $od ${CT:-120} $od.log
