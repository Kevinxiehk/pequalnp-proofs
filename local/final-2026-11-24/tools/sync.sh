#!/bin/bash
# Usage: sync.sh  -- sync the GitHub fork's main with upstream, fast-forward the local checkout if it is on main, list new Defs files
cd /home/kevxhk/code/pequalnp-proofs-2 || exit 2
OLD=$(git rev-parse upstream/main 2>/dev/null)
git fetch -q upstream main || { echo "fetch failed"; exit 1; }
NEW=$(git rev-parse upstream/main)
R=$(gh repo sync Kevinxiehk/pequalnp-proofs -b main 2>&1 | tail -1)
if echo "$R" | grep -qi "workflow\|error\|fail"; then
  git fetch -q origin main && git merge-base --is-ancestor origin/main upstream/main && git push -q origin upstream/main:main 2>/dev/null && R="ssh fast-forward to $(git rev-parse --short upstream/main) (gh sync needs workflow scope)" || R="FAILED: $R"
fi
echo "fork sync: $R"
[ "$(git branch --show-current)" = main ] && git merge -q --ff-only upstream/main 2>/dev/null
[ "$OLD" = "$NEW" ] && { echo "upstream unchanged at $(git log -1 --format=%h upstream/main)"; exit 0; }
echo "upstream $(echo $OLD | cut -c1-7) -> $(echo $NEW | cut -c1-7); changed Defs files:"
git diff --name-status "$OLD" "$NEW" -- lean/PEqualNP/Defs lean/PEqualNP/Defs.lean | head -20
