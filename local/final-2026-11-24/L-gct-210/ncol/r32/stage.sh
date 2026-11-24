#!/bin/sh
# stage.sh KIND OUTDIR UNITLOGS... : refine every non-UNIT two-zero chart of KIND (one = exactly one of delta, delta' pivots, no alpha;
# dd = both delta and delta', no alpha) using as UNIT set all charts reported UNIT in the given logs (names z_a_b_c_d.ms).
cd "$(dirname "$0")"
kind=$1; od=$2; shift 2
cat "$@" 2>/dev/null | grep ' UNIT ' | awk '{print $1}' | sed 's/^z_//; s/\.ms$//; s/_/,/g' | sort -u > $od.unit.txt
rm -rf $od; mkdir -p $od
for b in $(awk '{print $1}' repsz.txt | sed 's/,/_/g; s/^/z_/'); do
  S=$(echo $b | sed 's/^z_//; s/_/,/g')
  grep -qx "$S" $od.unit.txt && continue
  has0=$(echo ",$S," | grep -c ',0,'); has1=$(echo ",$S," | grep -c ',1,'); has2=$(echo ",$S," | grep -c ',2,')
  [ $has0 -eq 1 ] && continue
  n=$((has1+has2))
  if [ "$kind" = one ] && [ $n -ne 1 ]; then continue; fi
  if [ "$kind" = dd ] && [ $n -ne 2 ]; then continue; fi
  if [ "$kind" = none ] && [ $n -ne 0 ]; then continue; fi
  src=zfull/$b.ms; [ -f $src ] || src=zfull12/$b.ms; [ -f $src ] || src=zfull1/$b.ms
  python3 -I refine.py $src $od/$b.ms $S 13 $od.unit.txt orbz.py >> $od.gen.log
done
