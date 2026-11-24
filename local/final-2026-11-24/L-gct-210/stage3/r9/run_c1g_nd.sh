#!/bin/bash
ulimit -v 2500000
for p in 65521 2147483629 2147483497; do timeout 1700 python3 -I gen9.py $p C1G FULL 0 1; done
