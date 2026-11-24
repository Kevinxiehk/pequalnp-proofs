#!/bin/bash
cd "$(dirname "$0")"; : > res.log
for f in g_*.sing; do (ulimit -v 500000; timeout 300 Singular -q $f > ${f%.sing}.out 2>&1); echo "${f%.sing} $(grep -E 'VERDICT|halt' ${f%.sing}.out | head -1) $(grep FIBRES ${f%.sing}.out)" >> res.log; done; echo DONE >> res.log
