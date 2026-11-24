#!/bin/bash
ulimit -v 2500000
for m in near0.03 near0.1 near0.3; do timeout 700 python3 -I s3seed.py $m 0 3 0.0 0; done
timeout 900 python3 -I s3seed.py ext8 0 4 0.0 1
