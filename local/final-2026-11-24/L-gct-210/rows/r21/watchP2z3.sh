#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r21
while kill -0 768245 2>/dev/null; do sleep 20; done
sleep 5
echo "bq5R_P2_z3 (start 07:31, end $(date -u +%H:%M:%S)) | $(grep -v 'redefining\|^$\|^//' bq5R_P2_z3.out | tr -s '\n' ' ' | cut -c1-500)" >> kR2C.out
