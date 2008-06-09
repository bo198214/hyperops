"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Contributor: Jay D. Fox
Contributor: Wikipedia
Date: 2008-04-25
Description:

    hyperops/special/funcion.py contains definitions of special 
    functions, especially those that are required by or useful
    for use with tetration. Some of these special functions
    include: x^x, x^(1/x), the infinitely iterated exponential, 
    the Lambert W function, 
    
"""

from sage.all import *

def harmonic_number(n, k=1, r=1):
    """
    harmonic_number(n) -- n-th harmonic number
        gives SUM[i=1..n] 1/i

    harmonic_number(n, r=...) -- polylogarithmic harmonic numbers (standard)
        gives SUM[i=1..n] 1/i^r

    harmonic_number(n, k=...) -- Conway and Guy's harmonic numbers
        gives SUM[i=1..n] H(i, k=(k-1))

    harmonic_number(n, k, r) -- hybrid generalized harmonic numbers
        gives SUM[i=1..n] H(i, k=(k-1), r=r)
        there are certainly other ways of forming hybrids of these
        two generalizations, but this seemed the simplest to me.

    http://mathworld.wolfram.com/HarmonicNumber.html (uses n, k, r)
    """
    if k < 0:
        raise ValueError, "m must be positive"
    elif k == 0:
        ret = 1/(n**r)
    elif k == 1:
        # if QQ isn't used, then 1/n == 0 (integer division)
        ls = [QQ(1)/(j**r) for j in xrange(1, n + 1)]
        ret = sum(ls)
    else:
        ls = [harmonic_number(j, k - 1, r) for j in xrange(1, n + 1)]
        ret = sum(ls)
    return ret

def KnoebelH_by_iteration(x, guess=1):
    """
    KnoebelH_by_iteration(x)

    Inputs:   Flt:    A RealField of arbitrary precision
    Outputs:  a complex number with the same precision as Flt
    Description:
        Finds the upper primary fixed point of exponentiation for base e
    """
    # Notes:
    # 1) The code will loop until precision is within 8 bits of the full
    #    precision of the input field. However, the maxout variable is
    #    used to prevent an infinite loop, just in case.
    # 2) The perturb value is used to prevent a situation where the a0
    #    variable is so accurate that the axial variable can't be
    #    determined accurately. The number of bits of accyracy should
    #    roughly double with each iteration, so any inaccuracy introduced
    #    by perturb should easily be removed by another iteration.
    # Jay Fox's code (slightly modified for Sage 3.0 by AR):
    try:
        prec = x.prec()
    except:
        prec = 53
    R = RealField(prec)
    C = ComplexField(prec)    
    delta = R(2**(8-prec))
    perturb = C(2**(-3*prec/4), 0)
    a0 = C(0.3, 1.3)
    mag = 1
    maxout = 0
    while (mag > delta) and (maxout < 50):
        a0 = a0 + perturb
        a1 = C(log(a0)/log(x))
        #a1 = C(log(a0, x))
        diff = a1-a0
        axial = diff/(a0-1)
        mag = abs(diff)
        maxout = maxout + 1
        a0 = a1 + axial
    return a0
    
# The Knoebel H function
def KnoebelH(x, k=0):
    """
    KnoebelH(x) -- infinitely iterated exponential
    
    The Knoebel H function, also known as the infinite tetrate, or
    the infinitely iterated exponential, is defined as (x^^oo),
    but we use a different algorithm, obviously.
    """
    # FIXME: this needs work
    if x == 1:
        return 1
    elif x < 1/e:
        raise NotImplemented
    else:
        return KnoebelH_by_iteration(x)
    #return -LambertW(-log(x), k)/log(x)


# quote from Wikipediadef LambertW_by_desy(x):
    if x <= 500.0:
        lx1 = ln(x + 1.0)        return 0.665 * (1 + 0.0195 * lx1) * lx1 + 0.04    return ln(x - 4.0) - (1.0 - 1.0/ln(x)) * ln(ln(x))

# quote from Wikipediadef LambertW_by_iteration(x, prec=1E-12, maxiters=100, guess=0):    w = guess    for i in xrange(maxiters):        we = w*e**w        w1e = (w + 1)*e**w        if prec > abs((x - we) / w1e):            return w        w -= (we - x) / (w1e - (w+2) * (we-x) / (2*w+2))    raise ValueError("W doesn't converge fast enough for abs(z) = %f" % abs(x))

# The Lambert W function
def LambertW(x, k=0):
    """
    LambertW(x) -- base-e product logarithm
    """
    # FIXME: this needs work
    #w = var('w')
    #return series_inverse(w*e^w, x, w)
    if x == 0: return 0
    return LambertW_by_iteration(x, guess=LambertW_by_desy(x))
    #return KnoebelH(exp(-x), k)*x
