#!/bin/bash
# Usage: dupcheck.sh lean/PEqualNP/Outside/L_xxx.lean
# Refreshes the pull request heads of brilliant-hq/pequalnp-proofs (commits and trees only)
# and prints every pull request whose head contains that file, with author and date of its
# commit. It cannot tell open from closed; check the listed pull requests' pages for that.
set -u
P=$1
cd /home/claude/prscan || exit 2
git fetch -q --depth=2 --filter=blob:none upstream '+refs/pull/*/head:refs/prs/*' 2>/dev/null
git fetch -q --depth=1 --filter=blob:none upstream '+refs/heads/main:refs/upstream-main' 2>/dev/null
git cat-file -e "refs/upstream-main:$P" 2>/dev/null && echo "IN MAIN already"
git for-each-ref --format='%(refname:short)' refs/prs | while read -r r; do
  if git cat-file -e "$r:$P" 2>/dev/null && ! git cat-file -e "$r^:$P" 2>/dev/null; then
    echo "PR #${r#prs/}  $(git log -1 --format='%an  %cd' --date=format:'%H:%M %d-%b' "$r")"
  fi
done | sort -t'#' -k2 -n
