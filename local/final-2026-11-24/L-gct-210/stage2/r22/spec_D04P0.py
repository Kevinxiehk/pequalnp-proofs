sg=sp.Integer(0)
PAR=[]
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
BS=[mat({(1,0):sg,(2,0):-1-sg,(4,0):1}), mat({(3,0):-4,(3,1):1,(3,2):1,(3,3):1,(3,4):1}), mat({(3,1):1,(3,2):1,(3,3):-1,(3,4):-1}),
    mat({(4,1):1,(4,2):-1}), mat({(4,3):1,(4,4):-1})]
