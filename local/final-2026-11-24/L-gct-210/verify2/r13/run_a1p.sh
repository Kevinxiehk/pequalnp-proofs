#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r13
ulimit -v 2000000
for f in a1s3m_*_4_P1.sing; do timeout 300 Singular -q $f 2>&1 | grep A1S3 || echo "$f TIMEOUT/ERR"; done > a1p.log
echo done >> a1p.log
