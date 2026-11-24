#!/bin/bash
ulimit -v 2500000
while kill -0 48651 2>/dev/null; do sleep 5; done
for c in "C1G FULL 0 1" "C3c FULL 1 1" "C12ac FULL 1 1"; do timeout 1750 python3 -I exact9c.py $c 600 std 1; done
