#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/exact
for C in A B; do python3 -I gen_sym.py 2147483629 $C 3 /home/kevxhk/work/L-gct-210/verifyfl/r10/sym run timeout=60; done
echo SYM_DONE
