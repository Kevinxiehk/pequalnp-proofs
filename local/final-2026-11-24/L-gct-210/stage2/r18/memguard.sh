#!/bin/bash
# pause my small sequential job (r18/seq_small2.sh and descendants) when available memory < 1500 MB; resume above 2500 MB.
desc(){ local p=$1; echo $p; for c in $(ps -eo pid,ppid | awk -v p=$p '$2==p{print $1}'); do desc $c; done; }
paused=0
while true; do
  root=$(ps -eo pid,args | grep "[s]eq_small2.sh" | awk '{print $1}' | head -1)
  [ -z "$root" ] && { [ $paused = 1 ] || true; echo "$(date -u +%T) seq_small gone, guard exits"; exit 0; }
  av=$(free -m | awk '/Mem:/{print $7}')
  if [ "$av" -lt 1500 ] && [ $paused = 0 ]; then kill -STOP $(desc $root) 2>/dev/null; paused=1; echo "$(date -u +%T) paused (avail $av MB)"; fi
  if [ "$av" -gt 2500 ] && [ $paused = 1 ]; then kill -CONT $(desc $root) 2>/dev/null; paused=0; echo "$(date -u +%T) resumed (avail $av MB)"; fi
  sleep 30
done
