#!/bin/bash
# Round 13 watchdog (replaces watchdog12): stops ALL my pool jobs as soon as Lean window 3 opens
# (a runs/leanwindow3*.log containing "window: OPEN", or a new "paused" line in tools/leanwindow.log), at 05:30 UTC at the latest (coordinator: running through window 3 is fine).
# Bracket patterns, so nothing matches this script's own command line ("bash ./watchdog13.sh").
R=/home/kevxhk/work/runs; T=/home/kevxhk/work/tools/leanwindow.log; n0=$(grep -c "paused" $T 2>/dev/null)
while true; do
  if grep -qs "window: OPEN" $R/leanwindow3*.log; then why="Lean window 3 open"; break; fi
  if [ "$(grep -c "paused" $T 2>/dev/null)" -gt "$n0" ]; then why="leanwindow.sh pause (tools/leanwindow.log)"; break; fi
  if [ "$(date -u +%H%M)" -ge 0700 ]; then why="07:00 limit"; break; fi
  sleep 15
done
pkill -f "[c]hain13.sh" ; pkill -f "[c]hain13b.sh" ; pkill -f "[c]hain13c.sh" ; pkill -f "[c]hain13d.sh" ; pkill -f "[c]hain13e.sh" ; pkill -f "[c]hain14.sh" ; pkill -f "[c]hain14b.sh" ; pkill -f "[c]hain14c.sh" ; pkill -f "[c]hain14d.sh" ; pkill -f "[c]hain14e.sh" ; pkill -f "[c]hain14f.sh" ; pkill -f "[c]hain14g.sh" ; pkill -f "[c]hain15.sh" ; pkill -f "[c]hain15b.sh" ; pkill -f "[c]hain15c.sh" ; pkill -f "[c]hain15d.sh" ; pkill -f "[c]hain16.sh" ; pkill -f "[t]0_cell.py" ; pkill -f "[t]0b_cell.py" ; pkill -f "[r]adcell3g.py" ; pkill -f "[r]adcell3p.py" ; pkill -f "[r]adcell3r.py" ; pkill -f "[b]0sym_run.py" ; pkill -f "[s]ymdc_run.py" ; pkill -f "[r]adcell3.py" ; pkill -f "[r]adcell.py" ; pkill -f "[r]adcell2.py" ; pkill -f "[c]hain12.sh"
pkill -f "[t]0c_cell.py" ; pkill -f "[t]1_cell.py" ; pkill -f "[i]so_cell.py" ; pkill -f "[s]ym_cut3.py" ; pkill -f "[s]c0_fine.py" ; pkill -f "[p]1_cell.py" ; pkill -f "[a]nycell.py" ; pkill -f "[p]c_cell.py" ; pkill -f "[s]ym_cut4.py"
pkill -f "[m]solve -g 2 -t 1 -f t0/" ; pkill -f "[m]solve -g 2 -t 1 -f t1/" ; pkill -f "[m]solve -g 2 -t 1 -f iso/" ; pkill -f "[m]solve -g 2 -t 1 -f sc3/" ; pkill -f "[m]solve -g 2 -t 1 -f fine/" ; pkill -f "[m]solve -g 2 -t 1 -f p1/" ; pkill -f "[m]solve -g 2 -t 1 -f pc/" ; pkill -f "[m]solve -g 2 -t 1 -f sc4/" ; pkill -f "[m]solve -g 2 -t 1 -f rad/" ; pkill -f "[m]solve -g 2 -f symdc/" ; pkill -f "[m]solve -g 2 -t 1 -f b0/"
echo "$(date -u +%T) watchdog13: all verifyfl pool jobs stopped ($why)" >> /home/kevxhk/work/L-gct-210/verifyfl/r12/chain12.log
