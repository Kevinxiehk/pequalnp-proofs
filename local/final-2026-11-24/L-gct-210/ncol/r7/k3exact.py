# print the product structure of a K' hit: W_a (a-part) and W_b (b-part) in normalised form
import sys, numpy as np
w=np.exp(2j*np.pi/3); n1=np.array([1,w,w*w]); n2=np.array([1,w*w,w])
for f in sys.argv[1:]:
    Bq=np.load(f); Am=np.array([Y.T@n2/3 for Y in Bq]); Bm=np.array([Y.T@n1/3 for Y in Bq])
    # W_a = row space of Am, W_b = row space of Bm
    def rs(M):
        u,s,vh=np.linalg.svd(M); r=(s>1e-8*s[0]).sum(); V=vh[:r]
        # reduced row echelon (complex)
        V=V.copy(); piv=[]
        for i in range(r):
            j=np.argmax(abs(V[i])>1e-8) if False else None
        import sympy
        return V,r
    for name,M in (('W_a',Am),('W_b',Bm)):
        V,r=rs(M)
        # normalise: Gaussian elimination
        V=V.copy(); rows=[]; col=0; R=V
        R=R.copy(); r0=0; pivs=[]
        for c in range(5):
            if r0>=r: break
            i=r0+np.argmax(abs(R[r0:,c]))
            if abs(R[i,c])<1e-8: continue
            R[[r0,i]]=R[[i,r0]]; R[r0]/=R[r0,c]
            for k in range(r):
                if k!=r0: R[k]-=R[k,c]*R[r0]
            pivs.append(c); r0+=1
        R[abs(R)<1e-9]=0
        print(f,name,'dim',r); print(np.array2string(R,precision=4,suppress_small=True))
