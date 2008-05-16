# coding=latin-1
"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Date: 2008-04-22
Description:

    hyper/polynomial.py contains basic polynomials.
    a_poly(x) makes an arbitrary polynomial function, 
    and h_poly(x) and p_poly(x) make hyperbolic and parabolic 
    functions, respectively.
    
"""

from sage.all import *

def a_poly(x, n=5, coeff=[]):
    """
    a_poly(x) -- Arbitrary polynomial, with coeffs C1, C2, ...
    a_poly(x, n) -- Degree n polynomial, with coeffs C1, C2, ...
    a_poly(x, n, [a, b]) -- A polynomial starting with a + b*x + ...
    """
    if len(coeff) > n: n = len(coeff)
    head = [coeff[i]*x**i 
            for i in xrange(len(coeff))]
    tail = [var('C' + str(i))*x**i 
            for i in xrange(len(coeff), n + 1)]
    return sum(head + tail)

def h_poly(x, n=5):
    """
    h_poly(x) -- Hyperbolic polynomial
    """
    return a_poly(x, n, coeff=[0])

def p_poly(x, n=5):
    """
    p_poly(x) -- Parabolic polynomial
    """
    return a_poly(x, n, coeff=[0, 1])

# formerly coeffs_alist_to_vector
def get_coeff_list(ser, x, x0=0, n=5):
    # extract coeffs from series
    coeffs_alist = ser.coeffs(x)
    coeffs = [0 for k in xrange(n + 1)]
    for c in coeffs_alist:
        try:
            coeffs[int(c[1])] = c[0]
        except e:
            pass

    # make sure there are exactly (n+1) coeffs
    coeffs.extend([0 for i in xrange(n + 1 - len(coeffs))])
    coeffs = coeffs[0 : n + 1]
    return coeffs

