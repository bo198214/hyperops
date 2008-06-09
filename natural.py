"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Contributor: Jay D. Fox
Date: 2008-04-25
Description:

    hyperops/natural.py contains functions for use with
    natural iteration. In other words, iteration f<t>(x)
    by using power series in t or the inverse power series.
    
    "Natural" iteration starts with the natural Abel function.
    The natural Abel function is defined as the function whose
    coefficients (the vector c) satisfy the equation:
        
        R[f]*c = [1, 0, 0, 0, ..., 0]
    
    where R[f] is the Abel matrix of f(x).

    The Abel matrix was not defined by Abel himself, but was
    discovered by Andrew Robbins during the generalization
    of Peter Walker's work on the super-logarithm. The Abel
    matrix is roughly the result of applying the Bell matrix
    to both sides of the Abel functional equation:
    
        A(f(x)) = A(x) + 1
    
    once the natural Abel function is defined that satisfies
    this equation (as defined above), then the natural Schroeder
    function can be defined as S(x) = f'(x0)^A(x) so as to satisfy:
    
        S(f(x)) = f'(x0)^A(x) 
    
    known as the Schroeder functional equation.
    
"""

from sage.all import *
from hyper.special.matrix import Abel_matrix

def natural_Abel_function(expr, x, x0=0, n=5, rhs=[], ring=None):
    """
    natural_Abel_function(f(x), x)

    Returns a function, so to use this, write:
        a = natural_Abel_function(f(x), x)
    then you can do things like a(0), a(x), etc...
    """
    if rhs == []:
        rhs = [(1 if k == 0 else 0) for k in xrange(n)]
    if ring == None:
        ring = QQ
    abel = Abel_matrix(expr, x, x0, n)
    print rhs, type(rhs), type(abel)
    sol = abel.inverse()*vector(rhs)
    #sol = abel.solve_right(vector(ring, rhs))
    def ret(xf):
        return sum([sol[k]*xf**k for k in xrange(n)])
    return ret

def natural_Schroeder_function(expr, x, x0=0, n=5, fp=None, ring=None):
    """
    natural_Schroeder_function(f(x), x)

    Returns a function, so to use this, write:
        s = natural_Schroeder_function(f(x), x)
    then you can do things like s(0), s(x), etc...
    """
    abel = natural_Abel_function(expr, x, x0, n)
    if not fp == None:
        fp = diff(expr, x).subs(x=x0)
    def ret(xf):
        return fp**abel(xf)
    return ret
