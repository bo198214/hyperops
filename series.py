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
from special.matrix import Carleman_matrix

def series_inverse(expr, y, x, x0=0, n=5):
    """
    series_inverse(f(x), y, x) -- Lagrange reversion
    
    A better implementation of reversion(), because
    the one Sage has in sage/rings/power_series_poly.pyx
    called .reversion() is only implemented for QQ.
    
    The Lagrange-BŸrmann formula is:
    
        f<-1>(y) = x0 + SUM[n=1..] (y - y0)^n/n * ...
            ... [D_x^(n-1) ((x-x0)/(f(x)-y0))^n]_(x=x0)
    
    and since the expression after the "..." is a diagonal
    of a Bell or Carleman matrix, we use Carleman_matrix()
    to implement this function.
    """
    y0 = expr.subs(x=x0)
    
    # The Lagrange-BŸrmann formula
    carleman = Carleman_matrix((x - x0)/(expr - y0), x, x0, n + 1)
    # Convert matrix to lists
    carllist = map(list, list(carleman))    
    # Select lower off-diagonal
    cof = [carllist[k+1][k] for k in xrange(n + 1)]    
    # Add the constant term, and use coeffs
    return y0 + sum([cof[k]*y**(k+1)/(k+1) for k in xrange(len(cof))])

# I have an implementation of 'series_solve' in Mathematica, 
# but I have not re-written it for Sage yet. -- AR
def series_solve(expr, fx, x, x0=0, n=5, coeff=[]):
    """
    series_solve(g(x), f(x), x) -- Solve for f(x) in g(x) == 0.

    The series_solve() algorithm was designed for use with tetration.
    """
    #fn = a_poly(x + x0, n, coeff)
    pass