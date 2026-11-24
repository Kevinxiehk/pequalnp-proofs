#!/bin/bash
# mschart.sh DIR NAME [THREADS]: one msolve chart, stale-safe (output removed first; missing/old output = FAILED). Prints a VERDICT line.
d=$1; n=$2; th=${3:-1}; f=$d/$n.ms; o=$d/$n.out
rm -f $o
msolve -g 2 -t $th -f $f -o $o >/dev/null 2>&1; rc=$?
if [ ! -s $o ] || [ $o -ot $f ]; then echo "VERDICT mschart $d/$n: FAILED (rc=$rc, no fresh output)"; exit 0; fi
if grep -q '^\[1\]' $o; then echo "VERDICT mschart $d/$n: UNIT"; else echo "VERDICT mschart $d/$n: NONUNIT (rc=$rc, basis length $(grep -o 'length of basis: *[0-9]*' $o | grep -o '[0-9]*$'))"; fi
