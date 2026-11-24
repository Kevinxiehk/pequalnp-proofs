#!/bin/bash
# Stops the round-12 pool chain at 02:50 UTC (before the Lean window): chain12.sh (PID 381560) and its python / msolve children.
# Bracket patterns, so no pattern matches this script's own command line ("bash ./watchdog12.sh").
until [ "$(date -u +%H%M)" -ge 0250 ]; do sleep 20; done
kill 381560 2>/dev/null
pkill -f "[t]0c_cell.py" ; pkill -f "[t]1_cell.py" ; pkill -f "[i]so_cell.py" ; pkill -f "[s]ym_cut3.py"
pkill -f "[m]solve -g 2 -t 1 -f t0/" ; pkill -f "[m]solve -g 2 -t 1 -f t1/" ; pkill -f "[m]solve -g 2 -t 1 -f iso/" ; pkill -f "[m]solve -g 2 -t 1 -f sc3/"
echo "$(date -u +%T) watchdog: chain stopped" >> /home/kevxhk/work/L-gct-210/verifyfl/r12/chain12.log
