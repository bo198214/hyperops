"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Date: 2008-04-25
Description:

    hyper/parabolic.py 
    
"""

from sage.all import *
from special_matrices import Bell_matrix, Carleman_matrix

def safe_factor(x):
    if x == 0:
        return 0
    else:
        return factor(x)
    
def get_diagonal_power(expr, t, x, x0=0, n=5):
    fixp = diff(expr, x).subs(x=x0)
    ls = [fixp**(k*t) for k in xrange(n + 1)]
    return diagonal_matrix(ls)
    
# get_right_eigenvectors(h_poly(x), x)
def get_right_eigenvectors(expr, x, x0=0, n=5):
    bell = Bell_matrix(expr, x, x0, n)
    fixp = map(list, list(bell))[1][1]
    vars = vector([var('A'+str(k)) for k in xrange(n + 1)])
    ret = []
    ret.append([1] + [0 for k in xrange(n)])

    # this gives Inverse[p]
    # find eigenvectors, the first eigenvector will be
    # [1, 0, 0, ...] so we don't need to find it.
    for j in xrange(1, n + 1):
        sub = {}
        vec = []
        for k in xrange(0, j):
            sub['A'+str(k)] = 0
            vec.append(0)
        sub['A'+str(j)] = 1
        vec.append(1)

        # solve eigensystem equations
        eqns = (bell - (fixp**j)*identity_matrix(n + 1))*vars
        for k in xrange(j + 1, n + 1):
            #print "Eigenvector", j, sub
            try:
                eqn = eqns[k].subs(sub)
                #print "Equation", k, eqn
                if eqn == 0:
                    continue
                sol = solve(eqn, var('A'+str(k)))
                vec.append(sol[0][-1])
            except x:
                vec.append(1)
                raise x
            sub['A'+str(k)] = vec[-1]
        ret.append(vec)
    return matrix(ret)

def get_left_eigenvectors(expr, x, x0=0, n=5):
    carl = Carleman_matrix(expr, x, x0, n)
    fixp = map(list, list(carl))[1][1]
    vars = vector([var('A'+str(k)) for k in xrange(n + 1)])
    ret = []
    ret.append([1] + [0 for k in xrange(n)])

    # this gives Inverse[p]
    # find eigenvectors, the first eigenvector will be
    # [1, 0, 0, ...] so we don't need to find it.
    for j in xrange(1, n + 1):
        sub = {}
        vec = []
        for k in xrange(0, j):
            sub['A'+str(k)] = 0
            vec.append(0)
        sub['A'+str(j)] = 1
        vec.append(1)

        # solve eigensystem equations
        eqns = vars*(carl - (fixp**j)*identity_matrix(n + 1))
        for k in xrange(j + 1, n + 1):
            #print "Eigenvector", j, sub
            try:
                eqn = eqns[k].subs(sub)
                #print "Equation", k, eqn
                if eqn == 0:
                    continue
                sol = solve(eqn, var('A'+str(k)))
                vec.append(sol[0][-1])
            except x:
                vec.append(1)
                raise x
            sub['A'+str(k)] = vec[-1]
        ret.append(vec)
    return matrix(ret)
 
def is_hyperbolic(expr, x, x0):
    """
    is_hyperbolic(f(x), x, x0) -- is x0 a hyperbolic fixed point of f?
    """
    if expr.subs(x=x0) != x0:
        return False
    if diff(expr, x).subs(x=x0) == 1:
        return False
    return True

def hyperbolic_flow_coeffs(expr, t, x, x0=0, n=5, factor=True, check=True):
    """
    hyperbolic_flow_coeffs(f(x), t, x)
    """
    # is it a hyperbolic function?
    if check and not is_hyperbolic(expr, x, x0):
        raise ValueError, "x0 == f(x0) must be a hyperbolic fixed point (f'(x0) != 1)"
    # 'schr' is the Schroeder matrix, which is
    # actually the inverse of the standard 'P' in P*D*P^-1
    schr = get_left_eigenvectors(expr, x, x0, n)
    # the diagonal matrix to the t-th power
    diag = get_diagonal_power(expr, t, x, x0, n)
    
    # the Carleman matrix to the t-th power
    carl = (~schr)*diag*schr
    carl = map(list, list(carl))
    
    # coeffs of 1-st row
    cof = carl[1]
    if factor:
        ret = map(safe_factor, cof)
    else:
        ret = cof
    return ret

def hyperbolic_flow(expr, t, x, x0=0, n=5):
    """
    hyperbolic_flow(f(x), t, x)

    The power series (flow) for a hyperbolic function.
    Currently only implemented for a fixed point of 0.
    """
    # checks hyperbolic-ness
    coeffs = hyperbolic_flow_coeffs(expr, t, x, x0, n)
    return sum([coeffs[k]*(x - x0)**k for k in xrange(n + 1)])
