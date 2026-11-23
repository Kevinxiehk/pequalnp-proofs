import itertools, random
def perm3(A):
    return (A[0][0]*A[1][1]*A[2][2] + A[0][0]*A[1][2]*A[2][1] + A[0][1]*A[1][0]*A[2][2]
            + A[0][1]*A[1][2]*A[2][0] + A[0][2]*A[1][0]*A[2][1] + A[0][2]*A[1][1]*A[2][0])
random.seed(1)
ok=True
for r in range(3):
    for c in range(3):
        for _ in range(5):
            x=[[0]*3 for _ in range(3)]; y=[[0]*3 for _ in range(3)]
            for j in range(3): x[r][j]=complex(random.gauss(0,1),random.gauss(0,1))
            for i in range(3): y[i][c]=complex(random.gauss(0,1),random.gauss(0,1))
            P1=perm3([[1+x[i][j] for j in range(3)] for i in range(3)])
            P2=perm3([[1+y[i][j] for j in range(3)] for i in range(3)])
            P3=perm3([[1+x[i][j]+y[i][j] for j in range(3)] for i in range(3)])
            Y=sum(y[i][c] for i in range(3)); W=sum(x[r][j] for j in range(3))
            lhs=x[r][c]*y[r][c]
            rhs=(P3-6)-(1+Y/2-y[r][c]/2)*(P1-6)-(1-x[r][c]/2)*(P2-6)
            if abs(lhs-rhs)>1e-9: ok=False
            if abs((P1-6)/2-W)>1e-9 or abs((P2-6)/2-Y)>1e-9: ok=False
print("certificate ok:",ok)
out=[]
out.append("theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by\n  revert a\n  decide\n")
# rowsum
out.append("theorem n3_rowsum (x : Fin 3 × Fin 3 → ℂ) (r3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)\n    (h1 : pm (fun p => 1 + x p) = 6) : x (r3, 0) + x (r3, 1) + x (r3, 2) = 0 := by\n  simp only [pm, permanent_three, Matrix.of_apply] at h1\n  rcases fin3_cases r3 with rfl | rfl | rfl")
for r in range(3):
    facts=", ".join("hx %d %d (by decide)"%(i,j) for i in range(3) if i!=r for j in range(3))
    out.append("  · simp only [%s, add_zero] at h1\n    linear_combination h1 / 2"%facts)
out.append("")
out.append("theorem n3_colsum (y : Fin 3 × Fin 3 → ℂ) (c3 : Fin 3) (hy : ∀ i j, j ≠ c3 → y (i, j) = 0)\n    (h2 : pm (fun p => 1 + y p) = 6) : y (0, c3) + y (1, c3) + y (2, c3) = 0 := by\n  simp only [pm, permanent_three, Matrix.of_apply] at h2\n  rcases fin3_cases c3 with rfl | rfl | rfl")
for c in range(3):
    facts=", ".join("hy %d %d (by decide)"%(i,j) for i in range(3) for j in range(3) if j!=c)
    out.append("  · simp only [%s, add_zero] at h2\n    linear_combination h2 / 2"%facts)
out.append("")
out.append("theorem n3_alg (x y : Fin 3 × Fin 3 → ℂ) (r3 c3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)\n    (hy : ∀ i j, j ≠ c3 → y (i, j) = 0) (h1 : pm (fun p => 1 + x p) = 6)\n    (h2 : pm (fun p => 1 + y p) = 6) (h3 : pm (fun p => 1 + x p + y p) = 6) :\n    x (r3, c3) * y (r3, c3) = 0 := by\n  simp only [pm, permanent_three, Matrix.of_apply] at h1 h2 h3\n  rcases fin3_cases r3 with rfl | rfl | rfl <;> rcases fin3_cases c3 with rfl | rfl | rfl")
for r in range(3):
    for c in range(3):
        fx=", ".join("hx %d %d (by decide)"%(i,j) for i in range(3) if i!=r for j in range(3))
        fy=", ".join("hy %d %d (by decide)"%(i,j) for i in range(3) for j in range(3) if j!=c)
        Y="(y (0, %d) + y (1, %d) + y (2, %d))"%(c,c,c)
        out.append("  · simp only [%s, add_zero] at h1 h3\n    simp only [%s, add_zero] at h2 h3\n    linear_combination h3 - (1 + %s / 2 - y (%d, %d) / 2) * h1 - (1 - x (%d, %d) / 2) * h2"%(fx,fy,Y,r,c,r,c))
out.append("")
open("n3_alg.txt","w",encoding="utf-8").write("\n".join(out))
print(len("\n".join(out)))
