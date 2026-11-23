#!/bin/bash
# Usage: sync.sh
# Brings the GitHub fork's main branch and the shared local checkout up to date with the main
# project, rebuilds the project definitions if anything changed, and lists newly merged proof files.
set -u
REPO=/home/claude/pequalnp-proofs
cd "$REPO" || exit 2
OLD=$(git rev-parse HEAD)
git fetch -q --shallow-since="2026-11-23 06:00" upstream main 2>/dev/null || { echo "fetch failed"; exit 1; }
NEW=$(git rev-parse upstream/main)
echo "fork sync: $(git -c push.negotiate=true push origin upstream/main:refs/heads/main 2>&1 | tail -1)"
if [ "$OLD" = "$NEW" ]; then echo "local checkout already at $(git log -1 --format=%h)"; exit 0; fi
git checkout -q --detach upstream/main
echo "local checkout: $(echo $OLD | cut -c1-7) -> $(git log -1 --format='%h (%cd)' --date=format:'%H:%M')"
echo "new or changed files:"
git diff --name-status "$OLD" "$NEW" -- lean/PEqualNP 2>/dev/null | grep -vE 'Defs\.lean$' | head -40
source /root/.elan/env
( cd lean && lake build PEqualNP.Defs 2>&1 | grep -E 'error|completed|failed' | head -3 )
