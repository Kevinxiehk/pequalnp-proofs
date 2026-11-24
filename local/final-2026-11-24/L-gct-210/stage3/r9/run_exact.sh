#!/bin/bash
ulimit -v 2500000
timeout 1700 python3 -I exact9.py C1G FULL 0 1
timeout 1700 python3 -I exact9.py C3c FULL 1 1
timeout 1700 python3 -I exact9.py C12ac FULL 1 1
