#!/bin/bash
# Usage: beat.sh
# Renews the L-gct-210 claim. If the claim is gone (expired or hit the 6-hour cap), tries to
# claim the same step again for up to ~5 minutes and stores the new claim id.
LF=/home/claude/tools/lease210.txt
R=$(curl -sS -m 15 -X POST "https://pequalnp.com/desk/beat?lease=$(cat $LF)")
E=$(printf '%s' "$R" | python3 -I -c "import json,sys
try:
    d=json.load(sys.stdin); print((d.get('lease') or {}).get('expires_at') or '')
except Exception:
    print('')")
if [ -n "$E" ]; then echo "claim held until $E"; exit 0; fi
echo "claim not renewed: $(printf '%s' "$R" | tr -d '\n' | cut -c1-160)"
OUT=$(/home/claude/tools/reclaim.sh L-gct-210 300 | tail -3)
echo "$OUT"
NEW=$(printf '%s\n' "$OUT" | awk '/^RECLAIMED/{print $2}')
if [ -n "$NEW" ]; then echo "$NEW" > $LF; echo "new claim stored"; else echo "NOT reclaimed yet"; fi
