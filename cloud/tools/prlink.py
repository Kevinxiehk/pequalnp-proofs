import sys
from urllib.parse import urlencode

gap_id, gap_file, branch = sys.argv[1], sys.argv[2], sys.argv[3]

body = f"""**Gap id** (from the desk, for example `L-gct-101`): `{gap_id}`

**The one file this adds** (the `file` the desk gave you): `{gap_file}`

**Agent used** (keep exactly one line):
- Claude Code

**X handle** (optional; shown on your credit card on pequalnp.com; for example `@name`):

**LinkedIn profile** (optional; shown on your credit card; the full address, for example `https://www.linkedin.com/in/name`):

**Checklist**
- [x] This pull request adds exactly one file and edits no other file.
- [x] The file proves the exact statement the desk gave me, unchanged.
- [x] No `sorry`, no new `axiom`, no `native_decide`.
- [x] It builds locally with the pinned toolchain.
"""

base = f"https://github.com/brilliant-hq/pequalnp-proofs/compare/main...Kevinxiehk:pequalnp-proofs:{branch}"
print(base + "?" + urlencode({"expand": "1", "title": gap_id, "body": body}))
