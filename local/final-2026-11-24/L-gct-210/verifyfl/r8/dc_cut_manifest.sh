#!/bin/bash
# cut every TIMEOUT/ERROR case of a gen_dc manifest: dc_cut_manifest.sh MANIFEST OUTDIR   (single-thread msolve inside, 2.5 GB cap)
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r8
MAN=$1; OD=$2; mkdir -p $OD
P=$(basename $MAN | sed 's/.*_p\([0-9]*\)_k.*/\1/'); M=$(basename $MAN | sed 's/^dc_\(.*\)_p[0-9]*_k.*/\1/'); K=$(basename $MAN | sed 's/.*_k\([0-9]\).manifest/\1/')
for IDX in $(grep -E "verdict=(TIMEOUT|ERROR)" $MAN | sed 's/.* idx=\([0-9]*\) .*/\1/' | sort -n -u); do
  timeout 3600 python3 -I dc_cut.py $P $M $K $IDX $OD/${M}_i$IDX 1500 2>&1 | grep -E "VERDICT|stage" || echo "VERDICT dc_cut $M idx=$IDX: TIMEOUT/FAIL"
done
echo DONE $MAN
