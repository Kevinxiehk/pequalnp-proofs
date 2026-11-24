#!/bin/sh
# hiter.sh TC MAXPASS : fixed-point staged refinement for family TC over ALL orbit charts; each pass uses only charts verified before it.
cd "$(dirname "$0")"
tc=$1; maxp=$2
for pass in $(seq 1 $maxp); do
  od=hit_T${tc}_p$pass
  logs="hs3.log hs2.log hs2b.log hs1t2.log hs0t2.log hs0t0.log $(ls hit_T${tc}_p*.log 2>/dev/null)"
  cat $logs 2>/dev/null | grep " UNIT " | awk '{print $1}' | grep "_T$tc\.ms" | sed 's/^h_//; s/_T[0-9]\.ms$//' | sort -u > $od.done.txt
  before=$(wc -l < $od.done.txt)
  sed 's/_/,/g' $od.done.txt > $od.unit.txt
  rm -rf $od; mkdir -p $od
  for S in $(awk '{print $1}' repsh.txt); do
    n=$(echo $S | tr , _); grep -qx "$n" $od.done.txt && continue
    python3 -I hgen.py 65521 $S $tc $od/raw_${n}_T$tc.ms >/dev/null && (ulimit -v 2000000; timeout 120 Singular -q $od/raw_${n}_T$tc.sing >/dev/null 2>&1)
    python3 -I refine.py $od/raw_${n}_T$tc.ms $od/h_${n}_T$tc.ms $S 13 $od.unit.txt orbh.py >> $od.gen.log
    rm -f $od/raw_${n}_T$tc.*
  done
  left=$(ls $od/*.ms 2>/dev/null | wc -l)
  echo "pass $pass: verified before $before, charts left $left" >> hiter_T$tc.log
  [ "$left" -eq 0 ] && break
  (ulimit -v ${ULIM:-2000000}; ../gb/runlog.sh $od ${CT:-45} $od.log)
  new=$(grep -c ' UNIT ' $od.log)
  echo "pass $pass: new UNIT $new" >> hiter_T$tc.log
  [ "$new" -eq 0 ] && break
done
echo ITERDONE >> hiter_T$tc.log
