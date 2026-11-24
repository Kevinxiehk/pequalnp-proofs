#!/bin/sh
# hiter3.sh TYPE TC MAXPASS : fixed-point staged refinement for the H-conjecture, types b22 / b23 (hgen2.py, orbh2.py, repsh_TYPE.txt).
# Each pass uses only charts verified in earlier passes (sound, no circularity).  Env: ULIM (KB), CT (per-chart seconds).
cd "$(dirname "$0")"
ty=$1; tc=$2; maxp=$3; export TYPE=$ty
for pass in $(seq 1 $maxp); do
  od=h3_${ty}_T${tc}_p$pass
  cat $(ls h3_${ty}_T${tc}_p*.log 2>/dev/null) /dev/null | grep " UNIT " | awk '{print $1}' | sed 's/^h_//; s/_T[0-9]\.ms$//' | sort -u > $od.done.txt
  before=$(wc -l < $od.done.txt); sed 's/_/,/g' $od.done.txt > $od.unit.txt
  rm -rf $od; mkdir -p $od
  for S in $(awk '{print $1}' repsh_$ty.txt); do
    n=$(echo $S | tr , _); grep -qx "$n" $od.done.txt && continue
    python3 -I hgen2.py $ty 65521 $S $tc $od/raw_${n}_T$tc.ms >/dev/null && (ulimit -v 2000000; timeout 120 Singular -q $od/raw_${n}_T$tc.sing >/dev/null 2>&1)
    python3 -I refine.py $od/raw_${n}_T$tc.ms $od/h_${n}_T$tc.ms $S 13 $od.unit.txt orbh2.py >> $od.gen.log
    rm -f $od/raw_${n}_T$tc.*
  done
  left=$(ls $od/*.ms 2>/dev/null | wc -l); echo "pass $pass: verified before $before, charts left $left" >> hiter3_${ty}_T$tc.log
  [ "$left" -eq 0 ] && break
  (ulimit -v ${ULIM:-2000000}; ../gb/runlog.sh $od ${CT:-45} $od.log)
  new=$(grep -c ' UNIT ' $od.log); echo "pass $pass: new UNIT $new" >> hiter3_${ty}_T$tc.log
  [ "$new" -eq 0 ] && break
done
echo ITERDONE >> hiter3_${ty}_T$tc.log
