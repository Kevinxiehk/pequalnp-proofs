# verify2 r15: independent check of stage3 SR2111 configuration C*: row 1 carries span(n, z'), rows 2, 3 carry n, row 4 carries w (w not parallel
# to n), row 0 carries nothing.  Level <=> perm(J + Y) - 120 = 0 identically in (al, c1..c4), Y rows: 0; al z' + c1 n; c2 n; c3 n; c4 w.
# Charts: n_0 = 1 (column symmetry S_5), gauge z'_0 = 0 (z' mod n), z'_1 = 1 (S_4 on columns 1..4), w_k = 1, u (n_0 w_j - n_j w_0) = 1.
# usage: c_star_mine.py K J [drop3]
import sys, itertools
K,J=int(sys.argv[1]),int(sys.argv[2]); drop3=len(sys.argv)>3
P5=list(itertools.permutations(range(5)))
L=['ring R=0,(n1,n2,n3,n4,z2,z3,z4,w0,w1,w2,w3,w4,u,al,c1,c2,c3,c4),dp;','matrix Y[5][5];']
n=['1','n1','n2','n3','n4']; z=['0','1','z2','z3','z4']; w=['w%d'%i for i in range(5)]
rowsdef=[None,('al','z','c1','n'),('c2','n'),None if drop3 else ('c3','n'),('c4','w')]
for i in range(5):
    for c in range(5):
        if rowsdef[i] is None: L.append('Y[%d,%d]=1;'%(i+1,c+1))
        elif len(rowsdef[i])==4: L.append('Y[%d,%d]=1+al*(%s)+c1*(%s);'%(i+1,c+1,z[c],n[c]))
        else:
            v={'n':n,'w':w}[rowsdef[i][1]]; L.append('Y[%d,%d]=1+%s*(%s);'%(i+1,c+1,rowsdef[i][0],v[c]))
L.append('poly F=%s-120;'%'+'.join('*'.join('Y[%d,%d]'%(r+1,p[r]+1) for r in range(5)) for p in P5))
L.append('matrix M=coef(F,al*c1*c2*c3*c4); ideal E; int t; for(t=1;t<=ncols(M);t++){E=E,M[2,t];}')
L.append('E=E,w%d-1,u*(w%d-(%s)*w0)-1;'%(K,J,n[J]))
L.append('ring R2=0,(n1,n2,n3,n4,z2,z3,z4,w0,w1,w2,w3,w4,u),dp; ideal E=imap(R,E); option(redSB); ideal G=std(E); printf("Cstar%s w%d minor %d: unit %%s dim %%s",reduce(1,G)==0,dim(G)); quit;'%('-drop3' if drop3 else '',K,J))
open('cs_%d%d%s.sing'%(K,J,'_d' if drop3 else ''),'w').write('\n'.join(L)+'\n')
