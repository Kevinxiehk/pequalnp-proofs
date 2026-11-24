#!/bin/bash
# run the 16 split Case-C systems of one shape over Q, sequentially (resumable)
cd "$(dirname "$0")/case11/C3"; SH=$1
for f in C3_${SH}_*.sing; do o=${f%.sing}.out; grep -q STD $o 2>/dev/null && continue
  (ulimit -v 500000; timeout ${JT:-900} Singular -q $f > $o 2>&1); echo "$(date -u +%H:%M) ${f%.sing} $(grep -E 'STD|halt' $o | head -1)" >> ../../C3.log
done; echo "DONE $SH" >> ../../C3.log
