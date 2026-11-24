# msolve input -> Singular script printing whether the ideal is the unit ideal (independent check of msolve UNIT verdicts)
import sys
f,out=sys.argv[1:3]; L=open(f).read().split('\n'); v=L[0].strip(); p=L[1].strip(); body=''.join(L[2:]).strip().rstrip(',')
open(out,'w').write('ring R = %s, (%s), dp;\noption(redSB);\nideal I = %s;\nideal G = std(I);\n"UNIT", (size(G)==1 && deg(G[1])==0);\n"DIM", dim(G);\nquit;\n'%(p,v,body))
