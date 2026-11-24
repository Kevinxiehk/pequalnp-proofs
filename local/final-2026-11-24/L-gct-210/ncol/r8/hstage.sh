#!/bin/sh
# hstage.sh NS OUTDIR LOGS... : refine all H charts with NS s-pivots using orbit reps verified (T0 and T2 both UNIT) in LOGS
cd "$(dirname "$0")"
ns=$1; od=$2; shift 2
cat "$@" 2>/dev/null | grep ' UNIT ' | awk '{print $1}' | sed 's/^h_//; s/\.ms$//' > $od.all.txt
awk -F_T '{c[$1]++} END{for(k in c) if(c[k]==2) print k}' $od.all.txt | sed 's/_/,/g' > $od.unit.txt
rm -rf $od; mkdir -p $od
for S in $(awk '{print $1}' repsh.txt | awk -F, -v ns=$ns '{n=0; for(i=1;i<=NF;i++) if($i<=2) n++; if(n==ns) print}'); do
  n=$(echo $S | tr , _)
  for TC in 0 2; do
    python3 -I hgen.py 65521 $S $TC $od/raw_${n}_T$TC.ms >/dev/null && (ulimit -v 2000000; timeout 120 Singular -q $od/raw_${n}_T$TC.sing >/dev/null 2>&1)
    python3 -I refine.py $od/raw_${n}_T$TC.ms $od/h_${n}_T$TC.ms $S 13 $od.unit.txt orbh.py >> $od.gen.log
    rm -f $od/raw_${n}_T$TC.*
  done
done
