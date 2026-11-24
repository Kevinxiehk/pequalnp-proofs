#!/bin/bash
ulimit -v 2500000
timeout 1750 python3 -I exact9c.py C1G FULL 0 1 90
timeout 1750 python3 -I exact9c.py C3c FULL 1 1 90
timeout 1750 python3 -I exact9c.py C12ac FULL 1 1 90
