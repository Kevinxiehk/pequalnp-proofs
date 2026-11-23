#!/bin/bash
# Usage: poll20.sh
# Asks the desk once every 20 s, forever. A TRACTABLE step is kept: it is written to
# /home/claude/untrusted/desk/poll/kept.json and the script exits 0 (so it can be worked on).
# Any other step is released at once with reason=other.
set -u
D=/home/claude/untrusted/desk/poll
mkdir -p "$D"
while true; do
  START=$(date +%s)
  F="$D/p$(date -u +%H%M%S).json"
  curl -sS -m 15 "https://pequalnp.com/desk/next?handle=Kevinxiehk" -o "$F" 2>/dev/null
  R=$(python3 -I -c "
import json,sys
try:
    d=json.load(open(sys.argv[1]))
except Exception:
    print('BAD'); sys.exit()
g=d.get('gap'); l=d.get('lease') or {}
if not g: print('NOGAP'); sys.exit()
ctx=str(g.get('context','')); st=str(g.get('statement',''))
heavy = ('HasCircuitSize' in st) or ('finite case analysis' in ctx) or ('checked by evaluation' in ctx) or ('SEARCH GAP' in ctx)
print(('HEAVY' if heavy else 'KEEP'), g['id'], l.get('id'), ('tractable' if ctx.startswith('TRACTABLE') else 'open-hard'))
" "$F")
  echo "$(date -u +%H:%M:%S) $R"
  set -- $R
  case "$1" in
    KEEP)
      if grep -qx "$2" /home/claude/tools/submitted.txt; then
        curl -sS -m 15 -X POST "https://pequalnp.com/desk/release?lease=$3&reason=submitted" -o /dev/null; rm -f "$F"; echo "  skipped: already submitted"
      elif grep -qx "$2" /home/claude/tools/attempted.txt; then
        curl -sS -m 15 -X POST "https://pequalnp.com/desk/release?lease=$3&reason=out_of_time" -o /dev/null; rm -f "$F"; echo "  skipped: already tried"
      else
        GF=$(python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['gap']['file'])" "$F")
        DUP=$(/home/claude/tools/dupcheck.sh "$GF" | grep -vE "^PR #($(paste -sd'|' /home/claude/tools/ourprs.txt)) " | tr '\n' ' ')
        if [ -n "$DUP" ]; then
          curl -sS -m 15 -X POST "https://pequalnp.com/desk/release?lease=$3&reason=other" -o /dev/null; rm -f "$F"; echo "  skipped: others already on it: $DUP"
        else
          cp "$F" "$D/kept.json"; echo "KEPT $2 lease $3"; exit 0
        fi
      fi ;;
    HEAVY) curl -sS -m 15 -X POST "https://pequalnp.com/desk/release?lease=$3&reason=other" -o /dev/null; rm -f "$F" ;;
    *) rm -f "$F" ;;
  esac
  NOW=$(date +%s); W=$((20 - (NOW - START))); [ "$W" -gt 0 ] && sleep "$W"
done
