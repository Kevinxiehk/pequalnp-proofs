#!/bin/bash
# bigslot.sh CMD... : run a big-memory job in the shared big-memory slot (same lock as Lean compiles), pausing long-timeout jobs meanwhile.
# Priority: while a big job is WAITING it holds bigslot.prio, and new Lean compiles defer to it (a running compile is never pre-empted).
exec 8>/home/kevxhk/work/tools/bigslot.prio
flock 8
exec 9>/home/kevxhk/work/tools/leanslot.lock
flock 9
flock -u 8; exec 8>&-
/home/kevxhk/work/tools/leanwindow.sh pause
trap '/home/kevxhk/work/tools/leanwindow.sh resume' EXIT
"$@"
