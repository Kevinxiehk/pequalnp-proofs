# mk_r31.py OUT [cfg-subset-file]: concatenate the R3-1 blocks (generic cores, setup, dispatch lemmas, d = 5 machinery,
# all generated configurations, dispatch modulo the 12 survivors).
import sys, glob, os
Z = '/home/kevxhk/work/L-gct-210/lean/zbf/'
out = sys.argv[1]
generic = ['r10_1', 'r10_3', 'r10_4', 'r10_6', 'r10_8', 'r11_1', 'r12_0', 'r11_3', 'r11_4', 'r11_5', 'r11_6', 'r11_7',
           'r11_8', 'r11_9', 'r11_10', 'r11_11', 'r12_2', 'r12_3']
cfgs = sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/cfg_out/*.txt'))
parts = [open(Z + b + '.txt', encoding='utf-8').read().strip('\n') for b in generic]
parts += [open(c, encoding='utf-8').read().strip('\n') for c in cfgs]
parts.append(open(Z + 'r12_1_surv.txt', encoding='utf-8').read().strip('\n'))
txt = '\n' + '\n\n'.join(parts) + '\n'
open(out, 'w', encoding='utf-8').write(txt)
print(out, len(cfgs), 'configurations', len(txt.encode()), 'bytes', txt.count('\n'), 'lines')
