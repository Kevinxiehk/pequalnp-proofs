import sys
base, block, out = sys.argv[1], sys.argv[2], sys.argv[3]
t = open(base, encoding='utf-8').read()
b = open(block, encoding='utf-8').read()
endl = '\nend PEqualNP.Outside.L_gct_210_aux.ZBF\n'
assert t.count(endl) == 1
t = t.replace(endl, '\n' + b.strip('\n') + '\n' + endl)
t = t.replace('theorem PEqualNP.Outside.L_gct_210_zbf :', 'theorem PEqualNP.Outside.L_gct_210 :')
open(out, 'w', encoding='utf-8').write(t)
print(out, len(t.encode('utf-8')), t.count('\n'))
