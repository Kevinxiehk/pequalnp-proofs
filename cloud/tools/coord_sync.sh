#!/bin/bash
# Usage: coord_sync.sh
# Two-way sync with the coordination branch coord-L-gct-210 on the fork:
#  - pulls the other session's commits (it writes only under local/),
#  - refreshes cloud/ from the cloud workspace (notes, specs, scripts, data, latest Lean files),
#  - commits and pushes if anything changed,
#  - lists files under local/ that changed since the previous sync.
set -u
C=/home/claude/coord
cd "$C" || exit 2
BR=coord-L-gct-210
BEFORE=$(git rev-parse -q --verify HEAD 2>/dev/null || echo none)
if git ls-remote --exit-code origin "refs/heads/$BR" >/dev/null 2>&1; then
  git fetch -q origin "$BR" 2>/dev/null
  if [ "$BEFORE" = none ]; then git reset -q --hard FETCH_HEAD; else git merge -q --no-edit FETCH_HEAD 2>&1 | tail -2; fi
fi
python3 -I - <<'EOF'
import os, shutil, fnmatch
SRC = [("/home/claude/work/L-gct-210", "/home/claude/coord/cloud/L-gct-210"),
       ("/home/claude/work/L-gct-086", "/home/claude/coord/cloud/L-gct-086")]
SKIP = ["*_ok.lean", "FL.v*.lean", "*.log", "__pycache__", "*.pyc"]
def skip(name):
    return any(fnmatch.fnmatch(name, p) for p in SKIP)
for src, dst in SRC:
    for root, dirs, files in os.walk(src):
        dirs[:] = [d for d in dirs if not skip(d)]
        rel = os.path.relpath(root, src)
        os.makedirs(os.path.join(dst, rel), exist_ok=True)
        for f in files:
            if skip(f):
                continue
            s = os.path.join(root, f); d = os.path.join(dst, rel, f)
            try:
                if os.path.getsize(s) > 20 * 1024 * 1024:
                    continue
                if not os.path.exists(d) or os.path.getmtime(s) > os.path.getmtime(d) or os.path.getsize(s) != os.path.getsize(d):
                    shutil.copy2(s, d)
            except OSError:
                pass
EOF
git add -A cloud README.md 2>/dev/null
if ! git diff --cached --quiet; then
  git commit -q -F - <<'EOF'
coord: refresh cloud notes

Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01XinpLTZPfbDBjWwPAeP3hj
EOF
  git push -q origin "HEAD:refs/heads/$BR" 2>&1 | tail -2
  echo "pushed: $(git log -1 --format='%h %cd' --date=format:'%H:%M')"
else
  echo "nothing new to push"
fi
AFTER=$(git rev-parse HEAD)
if [ "$BEFORE" != none ] && [ "$BEFORE" != "$AFTER" ]; then
  echo "changed under local/ since last sync:"
  git diff --name-status "$BEFORE" "$AFTER" -- local | head -40
fi
