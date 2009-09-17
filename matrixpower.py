def matrixpower(A,t):
  (J,S) = A.jordan_form(transformation=True)
  sn = len(J.subdivisions[0])-1
  blocks=[J.subdivision(k,k) for k in range(sn)]
    
  rblocks = []
  for jb in blocks:
    N = jb.nrows()
    ev = jb[0,0]
    if N == 1:
      jb = matrix([[ev**t]])
    else:
      D = jb - ev*identity_matrix(N)
      jb = sum([binomial(t,n)*ev**(t-n)*D**n for n in range(N)])
    rblocks += [jb]
    
  J = block_diagonal_matrix(*blocks)
  return S * J * ~S
       
