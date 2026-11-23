#!/bin/bash
# Usage: reclaim.sh GAP_ID [MAX_SECONDS]
# Asks the desk once every 20 s until it hands out GAP_ID again; any other step is released at once
# (reason=other). On success writes the desk's answer to /home/claude/untrusted/desk/reclaim_GAP.json,
# prints "RECLAIMED <lease id> <expires>" and exits 0. Exits 1 after MAX_SECONDS (default 540).
set -u
GAP=$1
MAX=${2:-540}
D=/home/claude/untrusted/desk
T0=$(date +%s)
while [ $(( $(date +%s) - T0 )) -lt "$MAX" ]; do
  START=$(date +%s)
  F="$D/reclaim_try.json"
  curl -sS -m 15 "https://pequalnp.com/desk/next?handle=Kevinxiehk" -o "$F" 2>/dev/null
  R=$(python3 -I -c "
import json,sys
try:
    d=json.load(open(sys.argv[1]))
except Exception:
    print('BAD'); sys.exit()
g=d.get('gap'); l=d.get('lease') or {}
if not g: print('NOGAP'); sys.exit()
print(g['id'], l.get('id'), l.get('expires_at'))
" "$F")
  set -- $R
  if [ "$1" = "$GAP" ]; then
    cp "$F" "$D/reclaim_$GAP.json"; echo "RECLAIMED $2 $3"; exit 0
  elif [ "$1" != NOGAP ] && [ "$1" != BAD ]; then
    curl -sS -m 15 -X POST "https://pequalnp.com/desk/release?lease=$2&reason=other" -o /dev/null
    echo "$(date -u +%H:%M:%S) got $1, released"
  else
    echo "$(date -u +%H:%M:%S) $1"
  fi
  NOW=$(date +%s); W=$((20 - (NOW - START))); [ "$W" -gt 0 ] && sleep "$W"
done
exit 1
