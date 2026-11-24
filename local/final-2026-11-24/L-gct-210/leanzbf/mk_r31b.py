# mk_r31b.py OUT : the BUNDLED R3-1 block: generic cores, r13_1/r14_1/r15_1, the shared pattern lemmas (pat_out/pw_all.txt),
# per-configuration inst_<tag> (cfgb_out: gen_cfgp output, or gen_cfg5 output for the refused d = 5 configurations),
# the (E5) lemmas, the bundled survivor lemmas (survp_out), the dispatch r12_1_surv_b and r16_final (r31_hyp_full).
import sys, glob
Z = '/home/kevxhk/work/L-gct-210/lean/zbf/'
Y = '/home/kevxhk/work/L-gct-210/leanzbf/'
out = sys.argv[1]
generic = ['r10_1', 'r10_3', 'r10_4', 'r10_6', 'r10_8', 'r11_1', 'r12_0', 'r11_3', 'r11_4', 'r11_5', 'r11_6', 'r11_7',
           'r11_8', 'r11_9', 'r11_10', 'r11_11', 'r12_2', 'r12_3', 'r13_1', 'r14_1', 'r15_1']
files = [Z + b + '.txt' for b in generic] + [Y + 'pat_out/pw_all.txt']
files += sorted(glob.glob(Y + 'cfgb_out/*.txt')) + sorted(glob.glob(Y + 'e5_out/*.txt')) + sorted(glob.glob(Y + 'survp_out/*.txt'))
files += [Z + 'r12_1_surv_b.txt', Z + 'r16_final.txt']
txt = '\n' + '\n\n'.join(open(f, encoding='utf-8').read().strip('\n') for f in files) + '\n'
open(out, 'w', encoding='utf-8').write(txt)
print(out, len(files), 'files', len(txt.encode()), 'bytes', txt.count('\n'), 'lines')
