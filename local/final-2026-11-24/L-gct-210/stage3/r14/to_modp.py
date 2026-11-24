# Round 14: convert stage3's exact Singular scripts (over Q or Q(i)) to characteristic P1 = 2147483629 (I -> a square root of -1 mod P1).
# usage: python3 -I to_modp.py IN.sing OUT.sing
import sys, re
P=2147483629
g=next(x for x in range(2,1000) if pow(x,(P-1)//2,P)==P-1); I=pow(g,(P-1)//4,P); assert (I*I+1)%P==0
s=open(sys.argv[1]).read()
s=re.sub(r'ring (\w+)=\(0,I\),\(([^)]*)\),dp;\s*minpoly=I\^2\+1;', lambda m:'ring %s=%d,(%s),dp; number I=%d;'%(m.group(1),P,m.group(2),I), s)
s=re.sub(r'ring (\w+)=0,\(([^)]*)\),dp;', lambda m:'ring %s=%d,(%s),dp;'%(m.group(1),P,m.group(2)), s)
assert '(0,I)' not in s and 'ring R=0' not in s, 'unconverted ring'
open(sys.argv[2],'w').write(s); print('converted',sys.argv[1],'->',sys.argv[2],'I =',I)
