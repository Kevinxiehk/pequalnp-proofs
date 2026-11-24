#!/bin/bash
# leanwindow.sh pause|resume : SIGSTOP / SIGCONT the coordinator's LONG-TIMEOUT Groebner jobs (timeouts >= 3 h) so a Lean compile gets RAM.
# Only these patterns (never msolve cells with short timeouts, never helpers' own jobs):
#   rows R7-X4K/T3 Singular (k3/k4/k5/t3 at 2147...), stage2 ST2-S7' elimination Singular (*_elim.sing)
PIDF=/home/kevxhk/work/tools/leanwindow.pids
case "$1" in
  pause)
    pgrep -f "[S]ingular -q k[345]_2147[0-9]*\.sing|[S]ingular -q k[st][45]_[-+]*_2147[0-9]*\.sing|[S]ingular -q Dir_(D0[0-9]*|FP0d|FQ0d)_[A-Za-z0-9_]*(c0_v123|comp[A-Za-z0-9]*)_elim\.sing" > $PIDF
    for p in $(cat $PIDF); do kill -STOP $p 2>/dev/null; done
    echo "== leanwindow: paused $(wc -l < $PIDF) long-timeout Groebner jobs ($(date -u +%T))" ;;
  resume)
    [ -f $PIDF ] && for p in $(cat $PIDF); do kill -CONT $p 2>/dev/null; done
    echo "== leanwindow: resumed $( [ -f $PIDF ] && wc -l < $PIDF || echo 0) jobs ($(date -u +%T))"; rm -f $PIDF ;;
esac
