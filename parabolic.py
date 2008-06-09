"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Contributor: Jay D. Fox
Date: 2008-04-25
Description:

    hyper/parabolic.py contains functions to perform
    regular iteration on functions with parabolic
    fixed points, also known as "parabolic iteration"
    
    
"""

from sage.all import *
from hyper.polynomial import get_coeff_list

def is_parabolic(expr, x, x0):
    """
    is_parabolic(f(x), x, x0) -- is x0 a parabolic fixed point of f?
    
    The fixed point is not optional, it is required.
    """
    # initialize conditions
    f0 = expr.subs(x=x0) - x0
    f1 = diff(expr, x).subs(x=x0) - 1
    
    # test conditions
    if f0 == 0 and f1 == 0:
        return True

    # FIXME: I don't know how to make this better
    if abs(f0) < 2.0**(-15) and abs(f1) < 2.0**(-15):
        return True
    
    return False

def parabolic_IDM(expr, x, x0=0, n=5, check=True):
    """
    parabolic_IDM(f(x), x) -- parabolic iterate derivative matrix.

    Contains in each row the power series for each iterate
    where the columns represent the coefficients of the 
    power series. The IDM is a (n+1)*(n+1) matrix A where:
    A_j_k = 1/k! the k-th derivative of the j-th iterate of f
    evaluated at x=x0.
    """
    # is it a parabolic function?
    # the real parabolic-ness check
    if check and not is_parabolic(expr, x, x0):
        raise ValueError, "x0 == f(x0) must be a parabolic fixed point (f'(x0) == 1)"

    # initialize data
    ret = []
    ser = x

    # truncate power series each time,
    # because keeping useless coefficients
    # makes it so much slower. This is fast!
    for i in xrange(n + 1):

        # find Taylor series about x=x0
        ser = taylor(ser.subs(x=expr), x, x0, n)
        cof = get_coeff_list(ser, x, x0, n)
        ret.append(cof)

    # the coefficients of the identity function
    top = [0, 1] + [0 for i in xrange(n - 1)]
    return [top] + ret

def parabolic_flow_coeffs(expr, t, x, x0=0, n=5):
    """
    parabolic_flow_coeffs(f(x), t, x)
    """
    # get parabolic IDM, checks parabolic-ness
    idm = parabolic_IDM(expr, x, x0, n)

    # use Jabotinsky's formula (requires IDM)
    ret = [sum([(-1)**(m-k-1)*idm[k][m]*
        binomial(t, k)*binomial(t-k-1, m-k-1)
        for k in xrange(m)]) for m in xrange(n)]
    return ret

def parabolic_flow(expr, t, x, x0=0, n=5):
    """
    parabolic_flow(f(x), t, x)

    The power series (flow) for a parabolic function,
    which is a power series in x and t.

    This takes the flow coefficients (1-D list) and
    'removes' a dimension (0-D value).
    """
    # this also checks parabolic-ness
    coeffs = parabolic_flow_coeffs(expr, t, x, x0, n)
    return sum([coeffs[k]*(x - x0)**k for k in xrange(n)])

def parabolic_flow_matrix(expr, t, x, x0=0, n=5):
    """
    parabolic_flow_matrix(f(x), t, x)

    The flow matrix for a parabolic function,
    basically the coefficients of x and t.

    This takes the flow coefficients (1-D list)
    and 'creates' a dimension (2-D matrix).
    """
    # this also checks parabolic-ness
    coeffs = parabolic_flow_coeffs(expr, t, x, x0, n)
    ret = []

    # # extract coeffs from series
    # coeffs = ser.coeffs(x)
    # coeffs2 = [0 for k in xrange(n + 1)]
    # for cof in coeffs:
    #     try:
    #         coeffs2[cof[1]] = cof[0]
    #     except:
    #         pass

    for i in xrange(n):
        if (i < 2):
            ret.append([coeffs[i]])
        else:
            ser = coeffs[i]
            # cof = coeffs[i].expand().coeffs(t)
            # extract coeffs from series
            cof = get_coeff_list(ser, t, 0, i-1)
            ret.append(cof)
    return ret
