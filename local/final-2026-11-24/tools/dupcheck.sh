#!/bin/bash
# Usage: dupcheck.sh [lean/PEqualNP/Outside/L_gct_210.lean]   -- lists upstream PRs (open or closed) that touch the file, and whether it is on main
P=${1:-lean/PEqualNP/Outside/L_gct_210.lean}
gh api "repos/brilliant-hq/pequalnp-proofs/contents/$P" --silent 2>/dev/null && echo "IN MAIN already: $P"
gh pr list --repo brilliant-hq/pequalnp-proofs --state all --limit 400 --json number,title,author,state,createdAt,files \
  --jq ".[] | select(any(.files[]?; .path==\"$P\")) | \"PR #\(.number) \(.state) \(.author.login) \(.createdAt) \(.title)\""
gh pr list --repo brilliant-hq/pequalnp-proofs --state all --search "L-gct-210 in:title" --json number,title,author,state --jq '.[] | "title match: PR #\(.number) \(.state) \(.author.login) \(.title)"'
echo "dupcheck done $(date -u +%T)"
