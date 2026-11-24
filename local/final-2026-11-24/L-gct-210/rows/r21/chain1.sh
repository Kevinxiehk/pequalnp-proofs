#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r21
until grep -q "^DONE pgRFQ" kPG.out; do sleep 5; done
if ! grep "^pgRFQ " kPG.out | grep -q "unit 1"; then ./runPG.sh pgRFSQ; fi
