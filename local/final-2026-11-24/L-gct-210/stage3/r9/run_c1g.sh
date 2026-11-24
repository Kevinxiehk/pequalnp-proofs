#!/bin/bash
ulimit -v 2500000
timeout 1500 python3 -I gen9.py 65521 C1G FULL 1 0
timeout 1500 python3 -I gen9.py 65521 C1G LEVEL 1 0
timeout 1500 python3 -I gen9.py 65521 C1G LEVEL 0 0
