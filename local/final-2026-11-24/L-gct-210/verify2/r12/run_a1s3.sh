#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
for sg in ++++ +++- ++-+ ++-- +-++ +-+- +--+ +--- -+++ -++- -+-+ -+-- --++ --+- ---+ ----; do for fc in 0 1 2; do for nc in w c3; do
  python3 -I a1s3_mine.py $sg $fc $nc 4; timeout 300 Singular -q a1s3m_${sg}_${fc}_${nc}_4.sing 2>&1 | grep A1S3MINE || echo "A1S3MINE $sg f$fc $nc TIMEOUT/ERROR"
done; done; done > a1s3mine.log
echo done >> a1s3mine.log
