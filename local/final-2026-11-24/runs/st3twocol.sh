#!/bin/bash
# st3twocol.sh S I J I2 J2 P : one chart of stage3's unified (II)/(III) "x* has two nonzero columns" system (run_twocol.sh split per chart)
cd /home/kevxhk/work/L-gct-210/stage3/r16
S=$1; I=$2; J=$3; I2=$4; J2=$5; P=$6; ALG=slimgb; [ "$P" != "0" ] && ALG=std
f=$(python3 -I st2_bigQ.py twocol $S $I $J $ALG $P $I2 $J2)
echo "=== twocol $S $I$J $I2$J2 P=$P file $f start $(date -u +%H:%M)"
/usr/bin/time -f "time %e s, max %M KB" Singular -q $f 2>&1 | grep -v redefining
