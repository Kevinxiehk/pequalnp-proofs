#!/bin/sh
# hstage2.sh NS TC OUTDIR LOGS... : family TC (0: t'' = f1 + tp f2, 2: t'' = f2), charts with NS s-pivots not yet UNIT in that family,
# refined by all orbit reps whose chart in family TC is UNIT in LOGS (families are separately invariant closed systems / charts).
cd "$(dirname "$0")"
ns=$1; tc=$2; od=$3; shift 3
cat "$@" 2>/dev/null | grep " UNIT " | awk '{print $1}' | grep "_T$tc\.ms" | sed 's/^h_//; s/_T[0-9]\.ms$//' | sort -u > $od.done.txt
sed 's/_/,/g' $od.done.txt > $od.unit.txt
rm -rf $od; mkdir -p $od
for S in $(awk '{print $1}' repsh.txt | awk -F, -v ns=$ns '{n=0; for(i=1;i<=NF;i++) if($i<=2) n++; if(n==ns) print}'); do
  n=$(echo $S | tr , _)
  grep -qx "$n" $od.done.txt && continue
  python3 -I hgen.py 65521 $S $tc $od/raw_${n}_T$tc.ms >/dev/null && (ulimit -v 2000000; timeout 120 Singular -q $od/raw_${n}_T$tc.sing >/dev/null 2>&1)
  python3 -I refine.py $od/raw_${n}_T$tc.ms $od/h_${n}_T$tc.ms $S 13 $od.unit.txt orbh.py >> $od.gen.log
  rm -f $od/raw_${n}_T$tc.*
done
