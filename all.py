"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Contributor: Jay D. Fox
Date: 2008-04-25
Description:

    hyper/all.py 
    
    This is traditionally where Sage would put things to be
    included in the global namespace when you load the library.
    
    This would normally be accomplished with:
    
        from sage.all import *
        from hyper.all import *
    
    if you wanted to write your own modules to HyperSage.
    
"""

from hyper import (
    hyper, hyperlog, hyperroot,
    tetrate, superlog, superroot,
    pentate, pentalog, pentaroot)
    
from polynomial import (
    a_poly, h_poly, p_poly,
    get_coeff_list)

from series import (
    series_inverse, 
    series_solve)

from special.matrix import (
    Abel_matrix, Bell_matrix, Carleman_matrix,
    matrix_exp, matrix_log, matrix_power)

from special.function import (
    harmonic_number,
    KnoebelH, LambertW)

from iteration.hyperbolic import (
    is_hyperbolic, 
    hyperbolic_flow,
    hyperbolic_flow_coeffs,
    get_right_eigenvectors,
    get_left_eigenvectors)

from iteration.parabolic import (
    is_parabolic,
    parabolic_IDM,
    parabolic_flow,
    parabolic_flow_coeffs,
    parabolic_flow_matrix)

#from iteration.regular import (
#    iterational, iterational_coeffs,
#    iterational_matrix)

#from iteration.natural import (
#    natural_Schroeder_function,
#    natural_Abel_function)
