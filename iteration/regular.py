"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Contributor: Jay D. Fox
Date: 2008-04-25
Description:

    hyper/parabolic.py 
    
"""

from sage.all import *

def iterational_matrix(expr, x, x0=0, n=5):
    """
    iterational_matrix(f(x), x) -- matrix of coefficients C[j,k]
        where f<t>(x) = SUM[j=0..n, k=0..n] C[j,k]*t^j*x^k
    """
    # assume x0 is fixed point, check later
    # is the function parabolic or hyperbolic?
    if diff(expr, x).subs(x=x0) == 1:
        f = parabolic_flow(expr, t, x, x0, n)
    else:
        f = hyperbolic_flow(expr, t, x, x0, n)
    return NotImplemented

def iterational_coeffs():
    pass
    
def iterational(expr, t, x, x0=0, n=5):
    pass

def regular_Abel_function(expr, x, x0=0, n=5):
    pass
    
def regular_Schroeder_function(expr, x, x0=0, n=5):
    pass
