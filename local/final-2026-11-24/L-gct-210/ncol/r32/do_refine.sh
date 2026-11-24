#!/bin/sh
# build the UNIT orbit list from zfull.log and refine every two-zero chart that did not come out UNIT (FAILED/TIMEOUT, or moved to zfull12/)
cd "$(dirname "$0")"
grep ' UNIT ' zfull.log | awk '{print $1}' | sed 's/^z_//; s/\.ms$//; s/_/,/g' > unitz.txt
rm -rf zref; mkdir -p zref
for f in $(grep -v ' UNIT ' zfull.log | grep '\.ms' | awk '{print $1}') $(cd zfull12 && ls *.ms 2>/dev/null) $(cd zfull1 && ls *.ms 2>/dev/null); do
  b=$(basename $f .ms); S=$(echo $b | sed 's/^z_//; s/_/,/g')
  src=zfull/$b.ms; [ -f $src ] || src=zfull12/$b.ms; [ -f $src ] || src=zfull1/$b.ms
  python3 -I refine.py $src zref/$b.ms $S 13 unitz.txt orbz.py >> zref.gen.log
done
