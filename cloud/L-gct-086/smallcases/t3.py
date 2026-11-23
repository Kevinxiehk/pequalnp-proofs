import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from tangent import *
# n=4: sigma 4-cycle, tau 3-cycle on {0,1,2} fixing 3; N=12, E={1,2}
cases=[(4,[1,2,3,0],[1,2,0,3],12,[1,2]),
       (5,[1,2,3,4,0],[1,2,0,4,3],30,[2,3,4]),
       (6,[1,2,3,4,5,0],[1,2,3,4,0,5],30,[1,2,3,4]),
]
for n,sg,ta,N,E in cases:
    W=weight_space(n,sg,ta,N,E)
    d=len(W); rk=np.linalg.matrix_rank(W.reshape(d,-1))
    dc=max(np.abs(W.sum(1)).max(),np.abs(W.sum(2)).max())
    print(f'n={n} N={N} E={E}: dim {d} rank {rk} doubly-centred-defect {dc:.1e} worst|P_k| {check_numeric(W,n)[1:].max():.1e} ext-space dim {ext_space_dim(W,n)[0]}')
