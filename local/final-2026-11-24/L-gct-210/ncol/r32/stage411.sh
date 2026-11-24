#!/bin/sh
# stage411.sh OUTDIR LOGS... : refine every non-UNIT Gr(4,11) chart (g_S_JJ) using the orbit reps T0 whose four m'-charts are ALL UNIT in LOGS
# (then every chart (T, J) with T in orbit(T0) is empty, for every J, since S4 acts on (T, J) jointly).
cd "$(dirname "$0")"
od=$1; shift
cat "$@" 2>/dev/null | grep ' UNIT ' | awk '{print $1}' | sed 's/^g_//; s/\.ms$//' > $od.all.txt
awk -F_J '{c[$1]++} END{for(k in c) if(c[k]==4) print k}' $od.all.txt | sed 's/_/,/g' > $od.unit.txt
rm -rf $od; mkdir -p $od
for f in $(cat "$@" | grep -v ' UNIT ' | grep '\.ms' | awk '{print $1}'); do
  b=$(basename $f .ms); S=$(echo $b | sed 's/^g_//; s/_J[0-9]$//; s/_/,/g')
  src=g411/$b.ms; [ -f $src ] || src=g411z/$b.ms
  nz=$(echo ",$S," | tr "," "\n" | grep -cE "^(8|9|10)$")
  [ -n "$KZ" ] && [ "$nz" != "$KZ" ] && continue
  python3 -I refine.py $src $od/$b.ms $S 11 $od.unit.txt orb411.py >> $od.gen.log
done
