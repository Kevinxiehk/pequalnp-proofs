#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r24/r2
for f in m5_3 m5_4; do
  echo "== $f start $(date -u +%H:%M:%S)"
  ( ulimit -v 2000000; timeout 1800 /usr/bin/time -f '%e s %M KB rc=%x' Singular -q $f.sing 2>&1 | grep -v redefining )
  echo "== $f end $(date -u +%H:%M:%S)"
done
