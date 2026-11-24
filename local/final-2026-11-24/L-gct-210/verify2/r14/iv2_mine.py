# verify2 r14: independent generator for ncol THEOREM N2 (sub-case iv-2): 3-dim spaces Q of 4x4 matrices whose rows lie in U = span(u1,u2)
# (U = {x : sum x = 0, x_0 = x_1}: TWO EQUAL COLUMNS 0, 1 -- a LINEAR, hence closed, condition), such that Q is LEVEL (perm(J4 + q) = 24 on Q)
# and every 3x4 row deletion is level (P_1 = P_2 = P_3 = 0 of the 3x4 matrix, computed DIRECTLY from subpermanents, not via dot products).
# Q in Gr(3,8) (coefficients (s_i, p_i) of row i on (u1,u2)); chart I = 3 pivot coordinates (all 56 charts); prime P.
# usage: iv2_mine.py P [cal]    cal: U = span(chi, e_0 - e_3) with i = sqrt(-1) mod P (contains the known solutions C^S (x) chi)
import sys, itertools
P=int(sys.argv[1]); cal=len(sys.argv)>2
if cal:
    Ii=next(pow(g,(P-1)//4,P) for g in range(2,1000) if pow(g,(P-1)//2,P)==P-1); assert (Ii*Ii+1)%P==0
    u1=[1,Ii,P-1,P-Ii]; u2=[1,0,0,P-1]
else:
    u1=[1,1,-2,0]; u2=[0,0,1,-1]
charts=list(itertools.combinations(range(8),3))
P4=list(itertools.permutations(range(4)))
def gen(ch):
    names=[]; B=[]
    for k in range(3):
        row=[]
        for c in range(8):
            if c in ch: row.append('1' if ch.index(c)==k else '0')
            else:
                # reduced echelon: entries in pivot columns of OTHER rows are 0 (identity block); entries before a row's own pivot are free too (Pluecker chart = identity on I)
                nm='b%d_%d'%(k,c); names.append(nm); row.append(nm)
        B.append(row)
    L=['ring R=%d,(%s,y1,y2,y3),dp;'%(P,','.join(names)),'matrix Q[4][4];']
    for i in range(4):
        s='('+'+'.join('y%d*%s'%(k+1,B[k][2*i]) for k in range(3))+')'
        p='('+'+'.join('y%d*%s'%(k+1,B[k][2*i+1]) for k in range(3))+')'
        for j in range(4): L.append('Q[%d,%d]=%s*(%d)+%s*(%d);'%(i+1,j+1,s,u1[j],p,u2[j]))
    L.append('poly PL=%s-24;'%'+'.join('*'.join('(1+Q[%d,%d])'%(r+1,p_[r]+1) for r in range(4)) for p_ in P4))
    L.append('ideal E; matrix M; int k; M=coef(PL,y1*y2*y3); for(k=1;k<=ncols(M);k++){E=E,M[2,k];}')
    for i in range(4):
        rows=[r for r in range(4) if r!=i]
        p1='+'.join('Q[%d,%d]'%(r+1,c+1) for r in rows for c in range(4))
        p2='+'.join('(Q[%d,%d]*Q[%d,%d]+Q[%d,%d]*Q[%d,%d])'%(a+1,c+1,b+1,d+1,a+1,d+1,b+1,c+1) for a,b in itertools.combinations(rows,2) for c,d in itertools.combinations(range(4),2))
        p3='+'.join('+'.join('*'.join('Q[%d,%d]'%(rows[r]+1,cols[pp[r]]+1) for r in range(3)) for pp in itertools.permutations(range(3))) for cols in itertools.combinations(range(4),3))
        for nm,ex in (('A',p1),('B',p2),('C',p3)):
            L.append('poly D%s%d=%s; M=coef(D%s%d,y1*y2*y3); for(k=1;k<=ncols(M);k++){E=E,M[2,k];}'%(nm,i,ex,nm,i))
    L.append('ring R2=%d,(%s),dp; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E); printf("IV2MINE%s chart %s: unit %%s dim %%s",reduce(1,G)==0,dim(G)); quit;'%(P,','.join(names),'-CAL' if cal else '',''.join(map(str,ch))))
    return '\n'.join(L)+'\n'
for ch in charts:
    open('iv2m_%s%s.sing'%(''.join(map(str,ch)),'_cal' if cal else ''),'w').write(gen(ch))
print('written',len(charts))
