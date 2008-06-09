"""
Title: HyperOps - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Date: 2008-04-25
Description:

    tetrapoint.py is a module that provides a floating-point 
    class which uses tetration instead of exponentiation. The 
    main advantage of this is that there is practically no
    overflow, as the upper bounds are much, much higher.
    
"""

from sage.rings.ring import Field

class RealTetrationalField_class(RealDoubleField_class):
    def __call__(self, x):
        return RealTetrationalField(x)

class RealTetrationalElement(FieldElment):
    def __init__(self, x):
        self._parent = 0
        self._sign = 0
        self._recip = 0
        self._base = 2
        self._height = 0
        self._mantissa = 0
        pass

    def __add__(self):
        pass
    def __sub__(self, other):
        other2 = other
        other2.sign ^= 1
        return self + other2

    def __mul__(self):
        pass
    def __div__(self):
        other2 = other
        other2.recip ^= 1
        return self*other2

    def __pow__(self):
        pass

    def __xor__(self):
        print "This should never be called in Sage!"

_RTF = RealTetrationalField_class()

def RealTetrationalField():
    """
    Return the unique instance of the Real Double Field. 
    
    EXAMPLES: 
        sage: RealDoubleField() is RealDoubleField()
        True
    """
    global _RDF
    return _RDF

    
def is_RealTetrationalElement(x):
    return PY_TYPE_CHECK(x, RealTetrationalElement)
