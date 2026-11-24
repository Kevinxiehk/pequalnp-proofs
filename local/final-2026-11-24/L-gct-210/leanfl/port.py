import re, sys, os, json
# usage: port.py SRCDIR DSTDIR "parts" [statefile]
# Ports C-parts to a generic field Kf (section variable, instance hypotheses NeZero (N : Kf)).
SRC, DST, parts = sys.argv[1], sys.argv[2], sys.argv[3].split()
STATE = sys.argv[4] if len(sys.argv) > 4 else None
os.makedirs(DST, exist_ok=True)
NZ = 'nz128, nz256, nz2, nz3, nz5, nz4, nz6, nz8, nz9, nz10, nz12, nz15, nz16, nz18, nz20, nz24, nz30, nz32, nz36, nz40, nz45, nz48, nz60, nz64, nz72, nz96, nz120, nz144, nz288'
FD = 'field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])'
FIELD = '(first | ring1 | ' + FD + ')'
RINGT = '(first | ring1 | ' + FD + ' | ring_nf)'
IDC = r"A-Za-z0-9_'"
def tokre(name):
    return re.compile(r"(?<![A-Za-z0-9_'.])" + re.escape(name) + r"(?![A-Za-z0-9_'])")

state = {'undet': [], 'dep': [], 'fact': [], 'defs': []}
if STATE and os.path.exists(STATE):
    state = json.load(open(STATE))
undet = set(state['undet']); dep = set(state['dep']); fact = set(state['fact']); defs = set(state['defs'])

HDR_RE = re.compile(r'^(theorem|def|lemma|abbrev|noncomputable def) (\S+)')

def split_blocks(text):
    res = []; cur = None; pre = []
    for l in text.split('\n'):
        m = HDR_RE.match(l)
        if m:
            if cur is not None: res.append(cur)
            cur = [m.group(1), m.group(2), [l]]
        elif cur is not None:
            cur[2].append(l)
        else:
            pre.append(l)
    if cur is not None: res.append(cur)
    return pre, res

def sig_end(s):
    d = 0; i = 0
    while i < len(s) - 1:
        c = s[i]
        if c in '([{⟨': d += 1
        elif c in ')]}⟩': d -= 1
        elif s[i:i+2] == ':=' and d == 0: return i
        i += 1
    return len(s)

def explicit_groups(sig):
    # top-level ( ... ) groups before the first top-level ' : '
    out = []; d = 0; i = 0; start = None
    while i < len(sig):
        c = sig[i]
        if c in '([{⟨':
            if d == 0 and c == '(': start = i
            d += 1
        elif c in ')]}⟩':
            d -= 1
            if d == 0 and start is not None and c == ')':
                out.append(sig[start:i+1]); start = None
        elif c == ':' and d == 0 and sig[i:i+2] != ':=':
            break
        i += 1
    return out

KFTOK = re.compile(r"(?<![A-Za-z0-9_'.])(Kf|V4|M45|M55)(?![A-Za-z0-9_'])")

def basic(text):
    text = text.replace('ℂ', 'Kf')
    text = text.replace('Complex.I_mul_I', 'Ii_mul_Ii')
    text = text.replace('Complex.I', '(Ii : Kf)')
    for a in ['V4', 'M45', 'M55']:
        text = re.sub(r"(?<![A-Za-z0-9_'.])" + a + r"(?![A-Za-z0-9_'])", '(' + a + ' Kf)', text)
    return text

def insert_kf(body, names, skipname=None):
    # replace uses of undetermined names X by (X (Kf := Kf)); for defs skip inside non-vector [ ] lists and unfold lines
    if not names: return body
    pat = re.compile(r"(?<![A-Za-z0-9_'.@])(" + '|'.join(re.escape(n) for n in sorted(names, key=len, reverse=True)) + r")(?![A-Za-z0-9_'])")
    out = []; stack = []; i = 0; n = len(body)
    lines = body.split('\n')
    res_lines = []
    for ln in lines:
        st = ln.lstrip()
        unfold = st.startswith('unfold ') or st.startswith('delta ')
        pos = 0; buf = []
        j = 0
        while j < len(ln):
            c = ln[j]
            if c == '[':
                stack.append('v' if j > 0 and ln[j-1] == '!' else 'l')
                buf.append(c); j += 1; continue
            if c == ']':
                if stack: stack.pop()
                buf.append(c); j += 1; continue
            m = pat.match(ln, j)
            if m and (j == 0 or not re.match(r"[A-Za-z0-9_'.@]", ln[j-1])):
                nm = m.group(1)
                inlist = bool(stack) and stack[-1] == 'l'
                if nm == skipname and not buf_has_content(buf):
                    buf.append(nm)
                elif nm in defs and (inlist or unfold):
                    buf.append(nm)
                elif re.match(r"\s*\([A-Za-z_][A-Za-z0-9_']*\s*:=", ln[m.end():]):
                    buf.append(nm + ' (Kf := Kf)')
                else:
                    buf.append('(' + nm + ' (Kf := Kf))')
                j = m.end(); continue
            buf.append(c); j += 1
        res_lines.append(''.join(buf))
    return '\n'.join(res_lines)

def buf_has_content(buf):
    s = ''.join(buf)
    return not re.fullmatch(r'\s*(theorem|def|lemma|abbrev|noncomputable def)\s*', s)

NUMDIV = re.compile(r"/\s*\(?\s*\d")

FIELD2 = '(first | ' + FD + ' | ring1)'
def tactics(blocktext, bname=''):
    out = []
    for ln in blocktext.split('\n'):
        k = ln.find('linear_combination')
        if k >= 0 and '(norm' not in ln[k:k+25]:
            rest = ln[k + len('linear_combination'):]
            f = FIELD2 if NUMDIV.search(rest) else FIELD
            ln = ln[:k] + 'linear_combination (norm := ' + f[1:-1] + ')' + rest
        ln = re.sub(r"(?<![A-Za-z0-9_'.])ring(?![A-Za-z0-9_'])", RINGT, ln)
        if NOSIMP and not re.match(r'^(nz|zn)\d+$|^ne\d+_\d+$', bname):
            ln = re.sub(r"(?<![A-Za-z0-9_'.])norm_num(?![A-Za-z0-9_'])(?! \[)", 'norm_num [nzs, zns, nes]', ln)
            ln = re.sub(r"(?<![A-Za-z0-9_'.])norm_num \[(?!nzs)", 'norm_num [nzs, zns, nes, ', ln)
        out.append(ln)
    return '\n'.join(out)

def heartbeats(text):
    lines = text.split('\n')
    hdr = [i for i, l in enumerate(lines) if HDR_RE.match(l)]
    out = list(lines)
    ins = []
    for a, i in enumerate(hdr):
        j = hdr[a + 1] if a + 1 < len(hdr) else len(lines)
        body = '\n'.join(lines[i:j])
        if 'field (disch' not in body:
            continue
        m = re.match(r'^set_option maxHeartbeats (\d+) in$', lines[i - 1]) if i > 0 else None
        if m:
            out[i - 1] = 'set_option maxHeartbeats ' + str(max(4 * int(m.group(1)), 800000)) + ' in'
        else:
            ins.append(i)
    for i in reversed(ins):
        out.insert(i, 'set_option maxHeartbeats 800000 in')
    return '\n'.join(out)

report = []
patch_hits = {}
HEADER = open('/home/kevxhk/work/L-gct-210/leanfl/port_header.txt').read()
NOSIMP = os.environ.get('PORT_NOSIMP') == '1'
if NOSIMP:
    HEADER = HEADER.replace('@[simp] theorem', 'theorem')
BIGB = '[Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)]'
IIB = '[Fact (∃ i : Kf, i ^ 2 = -1)]'
CLOS = [('ii', IIB, {'Ii', 'Ii_mul_Ii'}, {'Ii', 'Ii_mul_Ii'}), ('big', BIGB, {'generic_t'}, set())]
closets = {'ii': set(state.get('fact', [])), 'big': set(state.get('big', []))}
PATCHES = json.load(open('/home/kevxhk/work/L-gct-210/leanfl/port_patches.json'))
for p in parts:
    raw = open(f'{SRC}/{p}.part').read()
    if p == 'pre':
        raw = raw.replace('namespace PEqualNP.Outside.L_gct_210_aux.FL\n', 'namespace PEqualNP.Outside.L_gct_210_aux.FLK\n')
        old = 'abbrev M55 := Fin 5 × Fin 5 → ℂ\n\nabbrev M45 := Fin 4 × Fin 5 → ℂ\n\nabbrev V4 := Fin 4 → ℂ\n'
        assert raw.count(old) == 1
        a, b = raw.split(old)
        text = basic(a) + HEADER + basic(b)
    else:
        text = basic(raw)
    pre, blocks = split_blocks(text)
    outb = []
    for kind, name, lines in blocks:
        bt = '\n'.join(lines)
        # signature
        se = sig_end(bt)
        sig = bt[:se]
        # first insert Kf for previously known undetermined names
        shadow = set()
        for x in undet:
            if x in ('Ii',):
                continue
            e = re.escape(x)
            bindl = False
            for ln0 in bt.split('\n'):
                mm = re.match(r'\s*(?:·\s*)?(obtain|rcases|rintro|choose|intro|intros|cases)\b(.*)', ln0)
                part = ''
                if mm:
                    kw, rest0 = mm.group(1), mm.group(2)
                    if kw == 'obtain':
                        part = re.split(r' : |:=', rest0)[0]
                    elif kw in ('rcases', 'cases'):
                        part = rest0.split(' with ', 1)[1] if ' with ' in rest0 else ''
                    elif kw == 'choose':
                        part = rest0.split(' using ', 1)[0]
                    else:
                        part = rest0
                if 'fun ⟨' in ln0:
                    part += ' ' + ln0[ln0.index('fun ⟨'):].split('=>')[0]
                if part:
                    if re.search(r'(?<![A-Za-z0-9_.\'])' + e + r'(?![A-Za-z0-9_\'])', part):
                        bindl = True
            if bindl or re.search(r'fun\s+[^\n=]*(?<![A-Za-z0-9_.])' + e + r'(?![A-Za-z0-9_\'])[^\n]*=>', bt) \
                    or re.search(r'(?:^|fun |∀ |∃ |\s)\((?:[A-Za-z0-9_\' ]*\s)?' + e + r'(?:\s[A-Za-z0-9_\' ]*)?\s:(?!=)', bt[:sig_end(bt)] if False else '') \
                    or re.search(r'(?:fun|∀|∃) \((?:[A-Za-z0-9_\' ]*\s)?' + e + r'(?:\s[A-Za-z0-9_\' ]*)?\s:(?!=)', bt) \
                    or any(re.search(r'(?<![A-Za-z0-9_.\'])' + e + r'(?![A-Za-z0-9_\'])', g[1:].split(' : ')[0]) for g in explicit_groups(bt[len(kind) + 1 + len(name):sig_end(bt)])) \
                    or re.search(r'(?:set|let|have|obtain)\s+' + e + r'\b', bt):
                shadow.add(x)
        if shadow:
            report.append(('shadow', p, name, ' '.join(sorted(shadow))))
        bt2 = insert_kf(bt, undet - shadow, skipname=name)
        sig2 = bt2[:sig_end(bt2)]
        body2 = bt2[sig_end(bt2):]
        scope = bt2 if kind in ('def', 'abbrev', 'noncomputable def') else sig2
        mentions_dep = any(tokre(x).search(scope) for x in dep if x != name) or KFTOK.search(scope)
        if mentions_dep:
            dep.add(name)
            groups = explicit_groups(sig2[len(kind) + 1 + len(name):])
            if not any(KFTOK.search(g) for g in groups):
                undet.add(name)
                report.append(('undet', p, name))
        if kind in ('def', 'abbrev', 'noncomputable def'):
            defs.add(name)
        for kind_c, binder, seeds, prewritten in CLOS:
            S = closets[kind_c]
            uses = name in seeds or any(tokre(x).search(bt2) for x in S if x != name and x not in shadow)
            if kind_c == 'ii':
                uses = uses or ('(Ii : Kf)' in bt2) or ('Ii_mul_Ii' in bt2)
            if uses:
                S.add(name)
                if name not in prewritten:
                    hdr = bt2.split('\n', 1)
                    h0 = hdr[0]
                    k = h0.index(name) + len(name)
                    h0 = h0[:k] + ' ' + binder + h0[k:]
                    bt2 = h0 + ('\n' + hdr[1] if len(hdr) > 1 else '')
                    report.append((kind_c, p, name))
        bt2 = tactics(bt2, name)
        outb.append(bt2)
    newtext = '\n'.join(pre) + ('\n' if pre else '') + '\n'.join(outb)
    for old, new, cnt in PATCHES:
        c = newtext.count(old)
        if c:
            newtext = newtext.replace(old, new)
            patch_hits[old] = patch_hits.get(old, 0) + c
    newtext = heartbeats(newtext)
    open(f'{DST}/{p}.part', 'w').write(newtext)
if STATE:
    json.dump({'undet': sorted(undet), 'dep': sorted(dep), 'fact': sorted(closets['ii']), 'big': sorted(closets['big']), 'defs': sorted(defs)}, open(STATE, 'w'))
for old, new, cnt in PATCHES:
    if patch_hits.get(old, 0) != cnt:
        print('PATCH COUNT MISMATCH', patch_hits.get(old, 0), cnt, old[:80])
for r in report: print(*r)
