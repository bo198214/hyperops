"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Date: 2008-04-22
Description:

    hyperops/special/matrix.py contains functions used throughout
    various methods of iteration. These functions include the
    Bell matrix, Carleman matrix, and functions for taking the
    exp, log, and non-integer power of such matrices.
    
"""

from sage.all import *
from polynomial import get_coeff_list

def Carleman_matrix(expr, x, x0=0, n_row=5, n_col=0, limit=False):
    """
    Carleman_matrix(f(x), x) -- Carleman matrix of f(x)
    Carleman_matrix(f(x), x, x0) -- Carleman matrix about x=x0
    Carleman_matrix(f(x), x, x0, n) -- (n+1)*(n+1) Carleman matrix

    The Carleman matrix,
    from which the other 2 matrices are derived
    """
    if n_col == 0: n_col = n_row

    # initialize data
    ser = 1
    ret = [[1] + [0 for k in xrange(n_col)]]
    for j in xrange(1, n_row + 1):
        
        # find Taylor series about x=x0
    	ser = taylor(ser*expr, x, x0, n_col)
        cof = get_coeff_list(ser, x, x0, n_col)
    	ret.append(cof)

    return matrix(ret)

def Bell_matrix(expr, x, x0=0, n_row=5, n_col=0):
    """
    Bell_matrix(f(x), x) -- Bell matrix of f(x)
    Bell_matrix(f(x), x, x0) -- Bell matrix about x=x0
    Bell_matrix(f(x), x, x0, n) -- (n+1)*(n+1) Bell matrix

    The Bell matrix,
    transpose of the Carleman matrix.
    """
    if n_col == 0: n_col = n_row

    # take matrix transpose
    carleman = Carleman_matrix(expr, x, x0, n_col, n_row)

    return transpose(carleman)

def Abel_matrix(expr, x, x0=0, n_row=5, n_col=0):
    """
    Abel_matrix(f(x), x) -- Abel matrix of f(x)
    Abel_matrix(f(x), x, x0) -- Abel matrix about x=x0
    Abel_matrix(f(x), x, x0, n) -- n*n Abel matrix

    The Abel matrix, a truncated (Bell - Identity) matrix.
    """
    if n_col == 0: n_col = n_row

    # truncate the last row
    n_row -= 1
    bell = Bell_matrix(expr, x, x0, n_row, n_col)
    bell = map(list, list(bell))

    # subtract the identity matrix
    abel = [[bell[j][k] - (1 if j == k else 0)
            for k in xrange(n_col + 1)] 
           for j in xrange(n_row + 1)]

    # truncate the first column
    abel = map(lambda x: x[1:], abel)

    return matrix(abel)

def is_TriangularMatrix(m):
    if not is_Matrix(m):
        return False
    raise NotImplemented

def matrix_exp(m):
    """
    matrix_exp(m) -- matrix exponential
    
    Currently only matrix(SR, ...) matrices have
    the .exp() method implemented in Sage. We can 
    simply convert all matrices to symbolic matrices 
    in order to use this method.
    
    SR is a builtin for 'symbolic expression ring'
    """
    # convert to symbolic matrix to use .exp()
    s = matrix(SR, m)
    return s.exp()

def matrix_log(m):
    raise NotImplemented

def matrix_power(m, n):
    if is_Integer(n):
        return m**n
    
    # make sure m is a matrix
    if not is_Matrix(m):
        raise ValueError, "m must be a matrix"
    
    raise NotImplemented

    # if m is triangular, use interpolation
    if is_TriangularMatrix(m):
        return []

    # otherwise, use exp(n log(m)) method
    return matrix_exp(matrix_log(m)*n)
    
    # otherwise, use eigensystem method
    return []
        

