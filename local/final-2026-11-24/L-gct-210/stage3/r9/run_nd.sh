#!/bin/bash
ulimit -v 2500000
for p in 65521 2147483629 2147483497; do
 for c in C3c C12ac; do timeout 1500 python3 -I gen9.py $p $c FULL 1 1; done
done
