#!/bin/bash
# Usage: poll.sh ROUNDS
# Each round: ask the desk up to 3 times (5 s apart). Keep the first TRACTABLE step
# (writes it to /home/claude/untrusted/desk/poll/kept.json and exits 0); release
# every other step with reason=other. Rounds start 3 minutes apart. Exits 1 if none found.
set -u
ROUNDS=${1:-3}
D=/home/claude/untrusted/desk/poll
mkdir -p "$D"
for r in $(seq 1 "$ROUNDS"); do
  START=$(date +%s)
  for t in 1 2 3; do
    F="$D/r$(date -u +%H%M%S)_$t.json"
    curl -sS -m 30 "https://pequalnp.com/desk/next?handle=Kevinxiehk" -o "$F"
    R=$(python3 -I -c "
import json,sys
try:
    d=json.load(open(sys.argv[1]))
except Exception:
    print('BAD'); sys.exit()
g=d.get('gap'); l=d.get('lease') or {}
if not g: print('NOGAP'); sys.exit()
print(('EASY' if str(g.get('context','')).startswith('TRACTABLE') else 'HARD'), g['id'], l.get('id'))
" "$F")
    echo "$(date -u +%H:%M:%S) round $r try $t: $R"
    set -- $R
    case "$1" in
      EASY) cp "$F" "$D/kept.json"; echo "KEPT $2 lease $3"; exit 0 ;;
      HARD) curl -sS -m 30 -X POST "https://pequalnp.com/desk/release?lease=$3&reason=other" -o /dev/null ;;
      NOGAP|BAD) break ;;
    esac
    sleep 5
  done
  if [ "$r" -lt "$ROUNDS" ]; then
    NOW=$(date +%s); W=$((180 - (NOW - START))); [ "$W" -gt 0 ] && sleep "$W"
  fi
done
exit 1
