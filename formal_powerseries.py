r"""
Cached formal powerseries and formal Laurant series in one variable

<Paragraph description>

EXAMPLES::

<Lots and lots of examples>

AUTHORS:
- Henryk Trappmann (2022-08-23): initial version
"""

# ****************************************************************************
#       Copyright (C) 2022 Henryk Trappmann <your email>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.calculus.functional import diff
from sage.functions.log import log,exp
from sage.functions.other import sqrt
from sage.matrix.constructor import matrix, identity_matrix
from sage.misc.misc_c import prod
from sage.misc.functional import n as num
from sage.functions.other import factorial
from sage.functions.other import binomial as buggybinomial
from sage.rings.integer import Integer
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_ring import PolynomialRing_field
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.power_series_ring_element import PowerSeries
from sage.rings.rational_field import QQ, RationalField
from sage.rings.rational import Rational
from sage.rings.real_mpfr import RR, RealField, RealField_class
from sage.rings.real_mpfr import RealLiteral
from sage.rings.ring import Ring
from sage.structure.element import RingElement
from sage.structure.sage_object import SageObject
from sage.symbolic.expression import Expression
from sage.symbolic.ring import SymbolicRing
from sage.categories.action import Action
from operator import mul, truediv, pow
from sage.symbolic.constants import pi
from sage.rings.qqbar import QQbar
from sage.symbolic.relation import solve
from sage.calculus.var import var


HintType = PolynomialRing(QQ, 't')


def binomial(x, y):
    if type(x) is RealLiteral and x == int(x):
        res = buggybinomial(int(x), y)
    else:
        res = buggybinomial(x, y)
    # if isinstance(x,FormalPowerSeries):
    #   res = x.parent().One
    #   for n in xrange(y):
    #     res *= x-n
    #   return res.lmul(x.parent().base_ring().one_element()/factorial(y))
    if isinstance(x, SageObject):
        X = x.parent()
        XB = X.base()
        if isinstance(y, SageObject):
            Y = y.parent()
        elif type(y) is int:
            Y = Integer(1).parent()
        R = res.parent()
        # print X.is_ring(), not X.is_field(), XB.is_field(), XB.has_coerce_map_from(Y)
        if X.is_ring() and not X.is_field() and XB.is_field() \
                and XB.has_coerce_map_from(Y) and R.is_field():
            # we want the result being of the same type as X
            # not the FractionField that buggybinomial returns
            res = X(res)
    return res


def decidable0(K):
    """
    Returns true if K has a decidable 0.
    For example powerseries have no decidable 0.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing,decidable0
    sage: decidable0(QQ)
    True
    sage: decidable0(FormalPowerSeriesRing(QQ))
    False
    """
    if K == Integer or K == int:
        return True
    if K == Rational:
        return True
    if isinstance(K, RationalField):
        return True
    if isinstance(K, RealField_class):
        return True
    if isinstance(K, PolynomialRing_field):
        return True
    #            if isinstance(K,RealField):
    #                return true
    #            if isinstance(K,ComplexField_class):
    #                return true
    return False


def _isnat(n):
    """
    Returns True if n is a non-negative int or Integer.

    sage: from sage.rings.formal_powerseries import _isnat
    sage: _isnat(5r)
    True
    sage: _isnat(5)
    True
    sage: _isnat(0)
    True
    sage: _isnat(-1r)
    False
    """
    if isinstance(n, int) or isinstance(n, Integer):
        if n >= 0:
            return True
    return False


def _assert_nat(n):
    """
    Throws an exception if not _isnat(n).
    sage: from sage.rings.formal_powerseries import _assert_nat 
    sage: #try:
    sage: #    _assert_nat(-1)                                             
    sage: #except AssertionError:
    sage: #    print 'bang'
    """
    assert _isnat(n), repr(n) + " must be natural number."


def mul_factorial(c, n):
    return c * factorial(n)


def div_factorial(c, n):
    return c / factorial(n)


class FormalPowerSeriesRing(Ring):
    def __init__(self, base_ring, is_decidable=None):
        """
        Returns the powerseries ring over base_ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ) 
        FormalPowerSeriesRing over Rational Field
        """
        Ring.__init__(self,base=base_ring)
        if base_ring is None:
            return
        self.K = base_ring
        if is_decidable is None:
            self.is_decidable = decidable0(base_ring)
        # self.is_decidable.__doc__ = \
        #    "is_one and is_zero can be decided in the base_ring"

        if not self.is_decidable:
            # even if the base_ring is undecidable we want predict in
            # certain cases the first two elements of the powerseries
            # particularly to decide whether the first item 0 is 0
            # and whether item 1 is 1
            self.hint_type = HintType

        def PSS(seq):
            """ sage: None   # indirect doctest """
            return self.by_list(seq)

        if self.K == int:
            self.K = Integer

        K = self.K
        if self.K == SymbolicRing:
            self.K0 = Integer(0)
            self.K1 = Integer(1)
        else:
            self.K0 = K.zero()
            self.K1 = K.one()

        self.Zero = Zero(self)
        self.One = One(self)
        self.Id = Id(self, min_index=1)
        self.Inc = Inc(self)
        self.Dec = Dec(self)
        self.Exp = Exp(self)
        self.Dec_exp = Dec_exp(self, min_index=1)
        self.Log_inc = Log_inc(self, min_index=1)
        self.Sin = Sin(self, min_index=1)
        self.Cos = Cos(self)
        self.Arcsin = Arcsin(self, min_index=1)
        self.Arctan = Arctan(self, min_index=1)
        self.Sinh = Sinh(self, min_index=1)
        self.Cosh = Cosh(self)
        self.Arcsinh = Arcsinh(self, min_index=1)
        self.Arctanh = Arctanh(self, min_index=1)
        self.Bernoulli = (self.Id / self.Exp.dec()).apply(mul_factorial)
        self.Bernoulli.__doc__ = """
        The n-th Bernoulli number is equal to 
        the n-th derivative of 1/(exp(x)-1) at 0.
        """
        self.Tan = Tan(self)
        self.Tanh = Tanh(self, min_index=1)
        self.Xexp = Xexp(self, min_index=1)
        self.Lambert_w = Lambert_w(self, min_index=1)
        self.Sqrt_inc = Sqrt_inc(self)

        # dont go into a recursion defining stirling1
        if isinstance(K, FormalPowerSeriesRing):
            return

        self.Stirling1 = Stirling1(self)

        #         def lehmer_comtet(n,k): #A008296
        #             """ sage: None   # indirect doctest """
        #             r = 0
        #             for l in range(k,n+1):
        #                 r += binomial(l, k)*k**(l-k)*self.Stirling1[n][l]
        #             return K(r)

        self.Lehmer_comtet = Lehmer_comtet(self)
        self.A000248 = self.Lehmer_comtet

        # self.selfpower_inc = PSF(lambda n: K(sum([ lehmer_comtet(n,k) for k in range(0,n+1))/factorial(n),K0))
        self.Selfpower_inc = Selfpower_inc(self)

        self.Superroot_inc = Superroot_inc(self)

        self.A003725 = A003725(self)

        self.Selfroot_inc = Selfroot_inc(self)

        self.Inv_selfroot_inc = Inv_selfroot_inc(self)

        # Mittag-Leffler polynomial cache
        self.mlpc = {}

    def is_zero(self):
        return False
        #return sum([abs(self[k]) for k in range(100)]) == self.K0

    # class FPSAction(Action):
    #     def __init__(self, G, S, is_left=True, op=None):
    #         super().__init__(G, S, is_left=is_left, op=op)
    #         self.S = S
    #         # print("G",self.G,"is_left", self.is_left())
    #
    #     def left_domain(self):
    #         if self.is_left():
    #             return self.S
    #         else:
    #             return self.G
    #
    #     def right_domain(self):
    #         if self.is_left():
    #             return self.G
    #         else:
    #             return self.S
    #
    #     def codomain(self):
    #         return self.S
    #
    #     def _act_(self,g,x):
    #         if self.op == mul:
    #             if self.is_left():
    #                 return g.rmul(x)
    #             else:
    #                 return g.lmul(x)
    #         if self.op == truediv:
    #             if self.is_left():
    #                 return g.rmul(1/x)
    #             else:
    #                 return g.reciprocal().lmul(x)
    #         if self.op == pow and not self.is_left():
    #             return g.lmul(log(x)).exp()
    #
    # def _get_action_(self, S, op, self_on_left):
    #     if self.K.has_coerce_map_from(S):
    #         print(op,pow)
    #         if op == mul or op == truediv or op is pow:
    #             return self.FPSAction(S, self, is_left=self_on_left, op=op)

    def __call__(self, p1=None, p2=None, p3=None, **kwargs):
        """
        Initialization by finite sequence of coefficients:
        Examples:
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: PQ = FormalPowerSeriesRing(QQ)
        sage: PQ([1,2,3])
        [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ([])
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        
        Initialization by coefficient function:
        Example:
        sage: PQ(lambda n: 1/factorial(n))
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]

        Initialization by expresion:
        Examples:
        sage: PQ(1+2*x+3*x^2,x)
        [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ(exp(x),x)
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        sage: PQ(ln(x),x,1)
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]

        Note: This is much slower than directly providing the coefficient function. 
        See also methods: by_const, by_undef, by_list, by_taylor, by_lambda

        Some base rings of a FormalPowerSeries are decidable, some not
        if you think, that the automatic detection is wrong
        you can explicitely specify with is_decidable option
        sage: FormalPowerSeriesRing(QQ).is_decidable   
        True
        sage: FormalPowerSeriesRing(PolynomialRing(QQ,'x')).is_decidable   
        True
        sage: FormalPowerSeriesRing(FormalPowerSeriesRing(QQ)).is_decidable    
        False
        """

        if isinstance(p1, Integer) or isinstance(p1, int) or isinstance(p1, Rational):
            return self.by_constant(p1)

        if isinstance(p1, SageObject) and self.K.has_coerce_map_from(p1.parent()):
            return self.by_constant(p1)

        if isinstance(p1, list):
            if p2 is None:
                return self.by_list(p1, **kwargs)
            return self.by_list(p1, p2)

        if isinstance(p1, Expression):
            if p3 is None:
                return self.by_taylor(p1, p2)
            return self.by_taylor(p1, p2, p3)

        if isinstance(p1, Polynomial):
            return self.by_polynomial(p1)

        if isinstance(p1, PowerSeries):
            return self.by_powerseries(p1)

        # TODO generator if isinstance(p1,

        if isinstance(p1, type(lambda n: 0)):
            if p2 is None:
                return self.by_lambda(p1, **kwargs)
            return self.by_lambda(p1, p2)

        if type(p1) is FormalPowerSeries:
            return self.by_

        if p1 is None:
            return self.by_undefined(p2)

        raise TypeError("unrecognized initialization input " + repr(type(p1)))

    def by_lambda(self, f, min_index=0):
        """
        Returns the powerseries with coefficients f(n).

        Alternative expression: 
            self.by_lambda(f) == self(f)
            self.by_lambda(f,min_index) == self(f,min_index)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.by_lambda(lambda n: 1/factorial(n))
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]

        Initialization as formal Laurant series:
        sage: P.by_lambda(lambda n: n,-3)               
        [-3, -2, -1; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, ...]

        Corruptly setting min_index=3
        sage: P.by_lambda(lambda n: n,3)
        [0, 0, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, ...]

        Note that functions can not be serialized/pickled.
        If you want to have a serializable/picklable object, you can derive
        from FormalPowerSeries and define the method coeffs.
        
        sage: from sage.rings.formal_powerseries import FormalPowerSeries
        sage: #class F(FormalPowerSeries):^J    def coeffs(self,n): return n 
        sage: #F(P)
        """
        res = FormalPowerSeries(self, f, min_index)
        if min_index != 0:
            return res.extinct_before(min_index)
        return res

    def by_iterator(self, g, min_index=0):
        """
        Returns a powerseries from the generator g.
        The powerseries coefficients start at min_index
        which is allowed be negative obtaining a formal Laurant series.
        
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.by_iterator(iter(ZZ),-2) 
        [0, 1; -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 7, -7, 8, -8, 9, -9, 10, -10, ...]
        """

        return Iterated(self, g, min_index)

    def by_undefined(self, min_index=0):
        """
        Returns an undefined powerseries. This is useful to use method `define'.

        Alternative expressions: 
            self.by_undefined() == self()
            self.by_undefined(m) == self(None,m)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P.by_undefined()         
        sage: a
        Undefined
        sage: P.by_undefined(2).min_index
        2
        """
        return FormalPowerSeries(self, min_index=min_index)

    def by_list(self, the_list, start=0):
        """
        Returns the powerseries with coefficients p[n] where
        p[n]==0 for 0<=n<start, p[m+start]==list[m] for all list indices m,
        and p[n]==0 for all later indices n.

        Alternative expression: 
            self.by_list(list) == self(list)
            self.by_list(list,start) == self(list,start)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)                         
        sage: f = P.by_list([1,2,3,4,5])
        sage: f
        [1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.by_list([1,2,3],5)
        [0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return List(self, the_list, start).reclass()

    def by_polynomial(self, p):
        """
        Returns the FormalPowerSeries from the given Polynomial.
        Alternative expression: self.by_polynomial(p) == self(p)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: PP = PolynomialRing(QQ,x)
        sage: P = FormalPowerSeriesRing(QQ)
        sage: pp = PP([1,2,3])
        sage: P.by_polynomial(pp)
        [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: x = PP(x)
        sage: P(2*x+x**2)
        [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        if p.parent() == self.base_ring():
            return self.by_constant(p)
        return self.by_list(p.padded_list())

    def by_powerseries(self, p):
        """
        Returns the FormalPowerSeries from the given PowerSeries.
        Alternative expression: self.py_powerseries(ps)==self(ps)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: PS = PowerSeriesRing(QQ,x)
        sage: FPS = FormalPowerSeriesRing(QQ)
        sage: FPS.by_powerseries(PS([0,1,2,3]))
        [0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return self.by_polynomial(p.polynomial())

    def by_formal_powerseries(self, p, conv=lambda x: x):
        """
        Returns the FormalPowerseries converted from p by conv.
        """

        return self.by_lambda(lambda n: conv(p[n]), p.min_index)

    def by_taylor(self, expr, v, at=0):
        """
        Returns the taylor series of `expr' with respect to `v' at `at'.

        Alternative expressions:
            self.by_taylor(expr,v) == self(expr,v)
            self.by_taylor(expr,v,at) == self(expr,v,at)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ) 
        sage: f = P.by_taylor(ln(x),x,1)   
        sage: f
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        """

        # print "after",min_index
        return Taylor(self, expr, v, at).reclass()

    def by_constant(self, c):
        """
        Returns the powerseries with coefficients [c,0,0,...].

        Alternative expression: self.by_constant(c) == self(c)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: f = P.by_constant(42)
        sage: f
        [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        if c == self.K0:
            return Zero(self)
        if c == self.K1:
            return One(self)
        return Constant(self, c)

    def is_field(self):
        """
        Returns True if self is a field, i.e. if it can be used as
        formal laurant series.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(IntegerRing()).is_field()
        False
        sage: FormalPowerSeriesRing(QQ).is_field()           
        True
        """
        return self.K.is_field()

    def is_commutative(self):
        """
        The powerseries is commutative if the base ring is.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(IntegerRing()).is_commutative()
        True
        """
        return self.K.is_commutative()

    def is_exact(self):
        """
        The powerseries is exact if the base ring is.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(RR).is_exact()
        False
        sage: FormalPowerSeriesRing(QQ).is_exact()           
        True
        """
        return self.K.is_exact()

    def is_finite(self):
        """
        Powerseries ring is never finite (except the base ring has only 1 element).
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ).is_finite()
        False
        """
        return False

    def zero(self):
        """
        Returns the zero element of this power series ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.zero()
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return self.Zero

    def one(self):
        """
        Returns the one element of this power series ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.one()
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return self.One

    def _repr_(self):
        """
        Description of this FormalPowerSeriesRing.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ)._repr_()            
        'FormalPowerSeriesRing over Rational Field'
        """
        return "FormalPowerSeriesRing over " + repr(self.K)

    # def _coerce_map_from_(self, T):
    #     """
    #     Returns true if type T can be coerced to a FormalPowerSeries
    #     with self as parent. This can be done always when
    #     T can be coerced to self.base_ring().
    #     This is used for operations like _lmul_ and _rmul_.
    #
    #     sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    #     sage: P = FormalPowerSeriesRing(RR)
    #     sage: P._coerce_map_from_(QQ)
    #     True
    #     sage: P._coerce_map_from_(int)
    #     True
    #     sage: P = FormalPowerSeriesRing(QQ)
    #     sage: P._coerce_map_from_(int)
    #     True
    #     sage: P._coerce_map_from_(RR)
    #     False
    #     """
    #     # print self.K, T,not self.K.coerce_map_from(T) == None
    #     if self.K.coerce_map_from(T) is not None:
    #         return True
    #     if isinstance(T, FormalPowerSeriesRing):
    #         return self.K.coerce_map_from(T.K) is not None
    #     return False

    def base_ring(self):
        """
        Returns the base ring of the powerseries ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ).base_ring() == QQ
        True
        """
        return self.K

    def _test(self):
        """
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        
        sage: P.Bernoulli
        [1, -1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, ...]

#         #takes too long:
#         sage: P(exp(x),x)-P.Exp
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(log(x+1),x) - P.Log_inc
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(cos(x),x)-P.Cos
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(sin(x),x)-P.Sin
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arcsin(x),x) - P.Arcsin
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arctan(x),x) - P.Arctan
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(sinh(x),x)-P.Sinh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(cosh(x),x)-P.Cosh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arcsinh(x),x)-P.Arcsinh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arctanh(x),x)-P.Arctanh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(sqrt(x+1),x)-P.Sqrt_inc
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(x*exp(x),x)-P.Xexp
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(exp(x)-1,x)-P.Exp.dec()
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: P.Exp.dec().reclass() | P.Log_inc 
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Sin | P.Arcsin 
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Tan | P.Arctan
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Tanh | P.Arctanh
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Xexp | P.Lambert_w
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Superroot_inc.dec().reclass() | P.Selfpower_inc
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Inv_selfroot_inc.dec().reclass() | P.Selfroot_inc
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: P.Superroot_inc ** P.Superroot_inc
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Tan - P.Sin / P.Cos
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Sin*P.Sin + P.Cos*P.Cos
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p = P([3,2,1])
        sage: p.rcp()*p
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]


        sage: P._test()
        """
        pass


# class UndefinedFormalPowerSeries(RingElement):
#     """
#     Undefined powerseries.
#     """
#     coeffs = None
#     def _repr_(a):
#         return "Undefined"


class FormalPowerSeries(RingElement):
    """
    Formal power series:

    A powerseries p is basically seen as an infinite sequence of coefficients
    The n-th coefficient is retrieved by p[n].

    EXAMPLES:
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: PQ = FormalPowerSeriesRing(QQ)
        sage: #Predefined PowerSeries
        sage: expps = PQ.Exp
        sage: expps.polynomial(10,x)
        1/362880*x^9 + 1/40320*x^8 + 1/5040*x^7 + 1/720*x^6 + 1/120*x^5 + 1/24*x^4 + 1/6*x^3 + 1/2*x^2 + x + 1
        sage: expps
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        sage: PQ.Zero
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ.One
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ.Id
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: #finite powerseries
        sage: p = PQ([1,2,3,4])
        sage: p.polynomial(10,x)
        4*x^3 + 3*x^2 + 2*x + 1
        sage: p
        [1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: one = PQ([1])
        sage: id = PQ([0,1])

        sage: #power series are just functions that map the index to the coefficient          
        sage: expps[30]
        1/265252859812191058636308480000000

        Formal Laurant Series can have negative minimum index
        sage: PQ(lambda n: n,-5)
        [-5, -4, -3, -2, -1; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, ...]

        Power series operations
        sage: p+p
        [2, 4, 6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p-p
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p*p
        [1, 4, 10, 20, 25, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: one/p
        [1, -2, 1, 0, 5, -14, 13, -4, 25, -90, 121, -72, 141, -550, 965, -844, 993, ...]
        sage: p.rcp()/p*p*p
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p**2
        [1, 4, 10, 20, 25, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: #composition only works for coefficient 0 being 0 in the second operand         
        sage: dexp = (expps - one).reclass()
        sage: expps(dexp)
        [1, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]

        sage: #we come into interesting regions ...
        sage: dexp(dexp)
        [0, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]
        sage: dexp.nit(2)
        [0, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]
        sage: dexp.it(-1)
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        sage: dexp.it(-1)(dexp)
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: hdexp = dexp.it(1/2)
        sage: hdexp
        [0, 1, 1/4, 1/48, 0, 1/3840, -7/92160, 1/645120, 53/3440640, -281/30965760, ...]
        sage: #verifying that shoudl be Zero                                                  
        sage: hdexp.it(2) - dexp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: #symbolic (parabolic) iteration                                                 
        sage: dexp.it(x)[5].coefficients()
        [[-1/180, 1], [1/24, 2], [-13/144, 3], [1/16, 4]]
        sage: q = dexp.it(1/x).it(x)

        sage: expand(q[3])
        1/6
        sage: dexp[3]
        1/6

        sage: #you can initialize power series with arbitrary functions on natural numbers    
        sage: #for example the power series of sqrt(2)^x can be given as
        sage: bsrt = FormalPowerSeriesRing(SR).by_taylor(sqrt(2)^x,x)

        sage: #making the 0-th coefficient 0 to get the decremented exponential 
        sage: dbsrt = bsrt.set_item(0,0)
        
        sage: #and now starting hyperbolic iteration
        sage: dbsrt2 = dbsrt.it(x).it(1/x)
        sage: #Sage is not able to simplify 
        sage: #simplify(dbsrt2[3])
        sage: #but numerically we can verify equality
        sage: RR(dbsrt2[3](x=0.73)-dbsrt[3]) < 10**(-18)
        True
    """

    is0 = False
    is01 = False

    def __init__(self, parent, f=None, min_index=None, base_ring=None):
        """
        Returns the formal powerseries. 
        
        This method should only be called from FormalPowerSeriesRing.
        See the description there how to obtain a FormalPowerSeries.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing,FormalPowerSeries
        sage: FormalPowerSeries(FormalPowerSeriesRing(QQ))
        Undefined
        """
        if parent is None:
            if base_ring is None:
                parent = FormalPowerSeriesRing(QQ)
            else:
                parent = FormalPowerSeriesRing(base_ring)

        RingElement.__init__(self, parent)

        if 'coeffs' not in self.__class__.__dict__:
            self.coeffs = f

        if min_index is None:
            min_index = 0
        self.min_index = min_index  # the minimal non-zero index
        self._memo = {}
        self._powMemo = {}
        self._itMemo = {}

        self.K = self.parent().K
        self.K0 = self.parent().K0
        self.K1 = self.parent().K1

        self.min_index = min_index

        if self.min_index > 0:
            self._subclass(FormalPowerSeries0)
        # if not f==None:
        #    self.reclass()

    #    def new(self,f=None,min_index=0,**kwargs):
    #        return type(self)(self.parent(),f,**kwargs)

    def item_is_zero(self, n):
        """
        In the case of a decidable base_ring just returns whether
        self[n] == 0. In the case of non-decidable base_ring tries to
        guess.
        """
        if self.parent().is_decidable:
            return self[n] == 0
        return self.hint[n] == 0

    def item_is_one(self, n):
        """
        In the case of a decidable base_ring just returns whether
        self[n] == 1. In the case of non-decidable base_ring tries to
        guess.
        """
        if self.parent().is_decidable:
            return self[n] == 1
        return self.hint[n] == 1

    def _subclass(self, T):
        """
        Makes the methods in T available to self.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: #class B:
        sage: #    def f(self): return 'B'
        sage: #b = P.Exp._subclass(B)                                         
        sage: #b.f()                                                          
        """
        if isinstance(self, T):
            return self

        #        if issubclass(T,self.__class__):
        #            self.__class__ = T
        #            return self
        #
        #        bs = ()
        #        for C in self.__class__.__bases__:
        #            if issubclass(T,C):
        #                assert not T == C
        #                bs += (T,)
        #            else:
        #                bs += (C,)
        #        self.__class__.__bases__ = bs

        class Sub(T, self.__class__):
            pass

        self.__class__ = Sub

        return self

    def new(self, f=None, min_index=None, **kwargs):
        """ 
        Returns a FormalPowerSeries from the same parent and class.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: p = FormalPowerSeriesRing(QQ)([1,2])
        sage: p.new(lambda n: n).parent() == p.parent()
        True
        sage: p = FormalPowerSeriesRing(QQ)([0,2])
        sage: type(p.new(lambda n: n)) == type(p)
        True
        sage: p = FormalPowerSeriesRing(QQ)([0,1])
        sage: type(p.new()) == type(p)
        True
        """
        res = FormalPowerSeries(self.parent(), f, min_index, **kwargs)
        if min_index is None:
            res.__class__ = self.__class__
            if isinstance(self, FormalPowerSeries0):
                res.min_index = 1
        return res

    #     def __nonzero__(self):
    #         """
    #         Returns always None,
    #         as it is not decidable whether a powerseries is 0.

    #         sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    #         sage: FormalPowerSeriesRing(QQ)(0).is_zero() == None
    #         """
    #         return None

    #     def is_one(self):
    #         """
    #         Returns always None,
    #         as it is not decidable whether a powerseries is 1.
    #         """
    #         return None

    def define(self, p):
        """
        Defines the power series self by another powerseries p 
        which is allowed to refer to self.

        For example one can define exp by taking the integral of its 
        derivative which is again exp: 

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: f = P.by_undefined()         
        sage: f.define(integral(f,1))      
        sage: f                            
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        
        Or generally one can define g = exp o f by taking the integral of
        g * f'. For example for f(x)=x**2, [0,0,1]:
        sage: g = P()
        sage: f = P([0,0,1])
        sage: fd = f.diff()
        sage: g.define(integral(g*fd,1))                  
        sage: g - (f | P.Exp)
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        self.coeffs = p.coeffs

    def __getitem__(self, n):
        """
        Returns the n-th coefficient of this powerseries: self[n].
        This is the coefficient of x^n.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3])[1] == 2
        True
        """

        if isinstance(n, slice):
            return [self[ii] for ii in range(0 if n.start is None else n.start, n.stop, 1 if n.step is None else n.step)]
            # return self.__getslice__(slice.start,slice.stop)
        if n not in self._memo:
            # self._memo[n] = simplify(expand(self.coeffs(n)))
            self._memo[n] = self.coeffs(n)
        return self._memo[n]

    def __getslice__(self, i, j):  # [i:j]
        """
        Returns the list of coefficients with indices in range(i,j).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n)[1:3]
        [1, 2]
        """
        print(i, j)

        return [self[k] for k in range(i, j)]

    def set_item(a, index, value):
        """
        Returns the powerseries that has a[index] replaced by value.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).set_item(1,42)
        [1, 42, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P([1,2]).set_item(0,0).min_index
        1
        """
        min_index = a.min_index
        if min_index == index and value == 0:
            min_index += 1
        if min_index == index + 1 and value != 0:
            min_index -= 1
        return a.new(lambda n: value if n == index else a[n], min_index)

    def __setitem__(a, item, value):
        """
        Replaces a[item] by value, returns None.
        item can also be a range with value being a sequence.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([1,2,3])
        sage: p[1] = 42
        sage: p
        [1, 42, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p = P([1,2])
        sage: p[0] = 0
        sage: p.min_index
        1


        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P(lambda n: n)
        sage: p[5:10] = [42,43,44,45,46]
        sage: p
        [0, 1, 2, 3, 4, 42, 43, 44, 45, 46, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, ...]
        sage: p = P([1,2])
        sage: p[0:1] = [0]
        sage: p.min_index
        1
        sage: p = P([0,2])
        sage: p[0]=3
        sage: p.min_index
        0
        """

        if isinstance(item, slice):
            i = item.start
            j = item.stop
            seq = value
            if item.step not in (1, None):
                raise ValueError('only step=1 supported')
            min_index = a.min_index
            min_s = j - i
            for k in range(0, j - i):
                if not seq[k] == 0:
                    min_s = k
                    break

            if i <= min_index <= i + min_s:
                min_index = i + min_s
            else:
                min_index = min(min_index, i + min_s)

            a.min_index = min_index
            f = a.coeffs
            a.coeffs = lambda n: seq[n - i] if i <= n < j else f(n)
        else:
            index = item
            a.set_item(index,value)
            min_index = a.min_index
            if min_index == index and value == 0:
                min_index += 1
            if min_index == index + 1 and value != 0:
                min_index -= 1

            a.min_index = min_index
            f = a.coeffs
            a.coeffs = lambda n: value if n == index else f(n)

    def extinct_before(a, min_index):
        """
        Returns the powerseries with elements before min_index replaced by 0.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n).extinct_before(5)
        [0, 0, 0, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, ...]
        """
        return ExtinctBefore(a, min_index)

    def reclass(p):
        """
        Recalculates the class of this object which possibly changes 
        to a subclass having more (and possibly different) operations 
        available. Returns p.

        Reclass queries p[0] and p[1], so for the sake of a lazy `define'
        this is not automatically done on creation.

        Due to implementation effort a reclassed object can not be 
        pickled/serialized with dumps.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing, FormalPowerSeries
        sage: from sage.rings.formal_powerseries import FormalPowerSeries0, FormalPowerSeries01
        sage: P = FormalPowerSeriesRing(QQ)
        sage: isinstance(P([0,1]).reclass(),FormalPowerSeries01)
        True
        sage: isinstance(P([0,2]).reclass(),FormalPowerSeries0)
        True
        sage: isinstance(P([1,1]).reclass(),FormalPowerSeries)
        True
        """

        if p.parent().is_decidable:
            min_index = max(2, p.min_index)
            for n in range(p.min_index, 2):
                if not p[n] == 0:
                    min_index = n
                    break
            p.min_index = min_index

            if p.min_index == 1 and p[1] == 1 and not isinstance(p, FormalPowerSeries01):
                return p._subclass(FormalPowerSeries01)

        if p.min_index <= 0:
            return p

        if p.min_index > 2 and not isinstance(p, FormalPowerSeries0):
            return p._subclass(FormalPowerSeries0)

        # p.min_index is either 1 or 2
        if hasattr(p, 'hint'):
            if p.hint[0] == 0:
                if p.hint[1] == 0:
                    p.min_index = 2
                else:
                    p.min_index = 1
                    if p.hint[1] == 1 and not isinstance(p, FormalPowerSeries01):
                        return p._subclass(FormalPowerSeries01)

        if not isinstance(p, FormalPowerSeries0):
            return p._subclass(FormalPowerSeries0)

        return p

    def crush(self):
        """
        If the base_ring of self is again a powerseries over base_ring2,
        then interpret the coefficient powerseries as a powerseries in the same
        variable and expand the resulting powerseries over base_ring2.

        
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FQ = FormalPowerSeriesRing(QQ)
        sage: g = FQ.Dec_exp.regit(FQ.Exp)    
        sage: g.parent()
        FormalPowerSeriesRing over FormalPowerSeriesRing over Rational Field
        sage: g.crush()
        [0, 1, 1/2, 2/3, 17/24, 59/80, 1099/1440, 47297/60480, 48037/60480, ...]
        
        sage: P = PolynomialRing(FQ,'p')
        sage: p = P.gen()
        sage: FP = FormalPowerSeriesRing(P)
        sage: FP.Dec_exp.regit(p).parent() == FP
        True

        sage: FFP = FormalPowerSeriesRing(FP)
        sage: h1 = FP([0,p])
        sage: h2 = h1.apply(lambda poly,n: poly(FQ.Exp),result_type=FFP)
        sage: h2.parent() == FFP
        True
        sage: h2[1] - FQ.Exp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: h2[2]
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: h3 = h2.regit(5)
        sage: (h3[1] - FQ.Exp**(5))[0:7]
        [0, 0, 0, 0, 0, 0, 0]
        sage: h4 = h3.crush()
        sage: h4.parent() == FQ
        True
        sage: (h4 - FQ.Id * FQ.Exp(FQ.Id * (p-1)))[0:7]
        [0, 0, 0, 0, 0, 0, 0]
        """

        return Crush(self)

    def apply(self, f, first=None, last=None, result_type=None, result_base_ring=None):
        """
        Returns the result of applying the function f(x,n) on each coefficient
        self[n].

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing, mul_factorial
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.apply(mul_factorial)
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ...]
        """

        return Apply(self, f, first=first, last=last, result_type=result_type, result_base_ring=result_base_ring)

    def inc(a):
        """
        Increment: a + One. 

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Zero.inc()
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Zero + P.One
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return IncMethod(a)

    def dec(a):
        """
        Decrement: a - One.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)

        sage: P.Zero.dec()
        [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return DecMethod(a)

    def smul(a, s):
        """
        Scalar multiplication with scalar s

        Alternative expression: a.smul(s) == s * a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([1,2,3])
        sage: p.smul(2)
        [2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: (2/3) * p
        [2/3, 4/3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        Alternative expression: a.smul(s) == a * s

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([1,2,3])
        sage: p.smul(2)
        [2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p * (2/3)
        [2/3, 4/3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return SMul(a, s)

    _lmul_ = smul
    _rmul_ = smul

    def add(a, b):
        """
        Addition of two powerseries.

        Alternative expression: a.add(b) == a+b

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]) + P([4,5,6])
        [5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        return Add(a, b)

    _add_ = add

    def sub(a, b):
        """
        Subtraction of two powerseries: a-b.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n) - P(lambda n: n)
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P([0,1]).sub(P([1,0]))
        [-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return Sub(a, b)

    _sub_ = sub

    def neg(a):
        """
        Negation of the powerseries a.

        Alternative expression a.neg() == -a.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: -P(lambda n: 1)
        [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, ...]
        """
        return Neg(a)

    _neg_ = neg

    def mul(a, b):
        """
        Multiplication of two powerseries.
        This a lazy algorithm: for initial 0 in a[k] and initial 0 in b[n-k] 
        the corresponding b[n-k] or a[k] is not evaluated.

        Alternative expression: a.mul(b) == a*b

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: 1) * P(lambda n:1)
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, ...]
        """
        # multiplication of two powerseries

        return Mul(a, b)

    _mul_ = mul

    def div(c, b):
        """
        Division.
        Alternative expression: c.div(b) == c/b

        Precondition: b != Zero
        It satisfies: a/b*b=a, a*b/b=a

        If c[0]==0 it returns a formal Laurant series, i.e. min_index < 0.

        This operation is not lazy in b, it retrieves values starting from 
        i=min_index until it finds b[i]!=0

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3])/P([2,3,4])
        [1/2, 1/4, 1/8, -11/16, 25/32, 13/64, -239/128, 613/256, 73/512, ...]
        sage: P.One/P(lambda n: (-1)**n)
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        b.min_index = b.order()

        return Div(c, b)

    _div_ = div

    def rcp(a):
        """
        Returns the reciprocal power series, i.e. One/a.
        a must not be Zero.
        If a[0] == 0 it returns a fromal Laurant series (min_index < 0).
        
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n:1).rcp()
        [1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.parent().One / a

    reciprocal = rcp

    def npow_mult(a, n):
        """
        Power with natural exponent n computed in the most simple way by
        multiplying the powerseries n times.
        This function is cached, it remembers the power for each n.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).npow(2)/P([1,2,3])
        [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        _assert_nat(n)

        if n == 0:
            return a.parent().One
        if n == 1:
            return a
        if n not in a._powMemo:
            n1 = n // 2
            n2 = n // 2 + n % 2
            a._powMemo[n] = a.npow_mult(n1) * a.npow_mult(n2)
        return a._powMemo[n]

    def _s(f, k, m, n):
        """
        Returns the sum over 
        m_1+2*m_2+...+k*m_k = n, m_0+m_1+...+m_k = m
        of 
        (m over m_1,m_2,...,m_k)* f[0]^{m_0} ... f[k]^{m_k}

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp._s(3,5,2)
        25/2
        """
        #        print k,m,n
        if (k, m, n) in f._powMemo:
            return f._powMemo[(k, m, n)]

        if m == 0:
            if n == 0:
                return 1
            return 0
        if k < f.min_index:
            return 0
        #        if n < f.min_index*m: #case only for speed optimizing
        #            return 0
        #         if k == f.min_index: #case only for speed optimizing
        #             if n == k*m:
        #                 return f[k]**m
        #             return 0
        #        print 'p'
        res = 0
        mk = 0
        while min(f.min_index * m, 0) + k * mk <= n and mk <= m:
            v = f._s(k - 1, m - mk, n - k * mk)
            if not v == 0:  # be lazy in evaluating f[k]
                if not mk == 0:  # be lazy in evaluating f[k]
                    v *= f[k] ** mk
                res += v * binomial(m, mk)
            mk += 1

        f._powMemo[(k, m, n)] = res
        return res

    def npow_combin(f, m):
        """
        Power with natural exponent m.
        Computed via the cominatorial way similar to Faa di Bruno's formula.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).npow_combin(2)/P([1,2,3])
        [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        _assert_nat(m)
        return Npow(f, m)

    npow = npow_mult

    def nipow(a, t):
        """
        Non-integer power of a (works also for integers but less efficiently). 
        a[0] must be nonzero and a[0]**t must be defined
        as well multiplication of t with all coefficients.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.nipow(1/2)
        [1, 1/2, 1/8, 1/48, 1/384, 1/3840, 1/46080, 1/645120, 1/10321920, ...]

        sage: PR = FormalPowerSeriesRing(RR)
        sage: PR.Exp.nipow(RR(0.5r)).n(20)                       
        [1.0000, 0.50000, 0.12500, 0.020833, 0.0026042, 0.00026042, 0.000021701, ...]
        """
        return Nipow(a, t)

    def pow(a, t):
        """
        The t-th (possibly non-integer) power of a.
        a[0]**t has to be defined.

        Alternative expression: a.pow(t) == a ** t

        It satisfies:
        a.nipow(0) = One
        a.nipow(1) = a
        a.nipow(s+t) == a.nipow(s)*a.nipow(t)

        See also: npow, nipow
        
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: 1).pow(-1)
        [1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: R = RealField(16)
        sage: P = FormalPowerSeriesRing(R)
        sage: P([1,2,3])**(RealNumber(-0.37r))
        [1.000, -0.7400, -0.09619, 1.440, -2.228, 0.6642, 4.092, -9.079, 6.390, ...]
        """

        if isinstance(t, FormalPowerSeries):
            P = a.parent()
            return (a.log() * t) | P.Exp
        if isinstance(t, Integer) or isinstance(t, int):
            if t >= 0:
                return a.npow(t)
            return a.rcp().npow(-t)
        return a.nipow(t)

    __pow__ = pow

    def sqrt(a):
        """
        Square root of a. a.sqrt() * a.sqrt() == a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,1]).sqrt()
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: (P.One - P.Sin ** 2).sqrt() - P.Cos
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.rt(2)

    def rt(a, n):
        """
        n-th root of a. a.rt(n)**n == a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        
        sage: P([1,3,3,1]).rt(3)
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.nipow(1 / Integer(n))

    def compose(b, a):
        """
        Composition (left after right), in mathematical notation b o a.
        Alternative expressions: b.compose(a) == b(a) == a | b
        
        Precondition: 
            a[0] == 0. 
        Satisfies:
            a(b).polynomial(m*n,x) == a.polynomial(m,b.polynomial(n,x)) 

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).compose(P([0,1,2]))
        [1, 2, 7, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P([1,2,3])(P([0,1,2]))
        [1, 2, 7, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        a._assertp0()

        return Compose(b, a)

    __call__ = compose

    def log(a):
        """
        Logarithm of powerseries a with a[0]!=0.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.log()           
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        P = a.parent()

        divdec_a = (a.smul(a.K1/a[0])).set_item(0, 0)

        #        if decidable0(a.K):
        #            assert a[0] == 1
        return (divdec_a | P.Log_inc).set_item(0,log(a[0]))

    def exp(a):
        """
        Exponential of Powerseries
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: PQ = FormalPowerSeriesRing(QQ)
        sage: PQ.Log_inc.exp()
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ([2/3,5]).log().exp()
        [2/3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ([2/3,5]).exp().log()
        [2/3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        P = a.parent()

        return P.Exp(a.set_item(0,0)).smul(exp(a[0]))

    #     def __xor__(a,t): # ^
    #         #Not recognized as it seems to be mapped to ** in sage
    #         return NotImplemented

    def bell_polynomials(a, k):
        """
        The sequence of Bell polynomials (partial/of the second kind)
        [B_{0,k}(a[1],a[2],...),B_{1,k}(a[1],a[2],...),...]

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = PolynomialRing(QQ,['c1','c2','c3','c4','c5'])
        sage: c1 = P('c1'); c2= P('c2'); c3 = P('c3'); c4 = P('c4'); c5 = P('c5')
        sage: c = FormalPowerSeriesRing(QQ)([0,c1,c2,c3,c4,c5])
        sage: c.bell_polynomials(2)[6] == 6*c5*c1 + 15*c4*c2 + 10*c3**2
        True
        """
        A = a
        return (a.apply(div_factorial) ** k).apply(mul_factorial).smul(Integer(1) / factorial(k))

    def bell_polynomial(a, n, k):
        """
        The Bell polynomial (partial/of the second kind).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = PolynomialRing(QQ,['c1','c2','c3','c4','c5'])
        sage: c1 = P('c1'); c2= P('c2'); c3 = P('c3'); c4 = P('c4'); c5 = P('c5')
        sage: c = FormalPowerSeriesRing(QQ)([0,c1,c2,c3,c4,c5])
        sage: c.bell_polynomial(6,3) == 15*c4*c1**2 + 60*c3*c2*c1 + 15*c2**3
        True
        sage: c.bell_polynomial(6,2) == 6*c5*c1 + 15*c4*c2 + 10*c3**2
        True
        """
        return a.bell_polynomials(k)[n]

    def bell_complete(a, n):
        """
        The complete Bell polynomial.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing, div_factorial
        sage: P = PolynomialRing(QQ,['c1','c2','c3','c4','c5'])
        sage: c1 = P('c1');c2 = P('c2');c3 = P('c3');c4 = P('c4');c5 = P('c5')
        sage: PS = FormalPowerSeriesRing(P)
        sage: c = PS([0,c1,c2,c3,c4,c5])
        sage: (PS.Exp(c.apply(div_factorial)) - c.bell_complete(5).apply(div_factorial))[1:6]
        [0, 0, 0, 0, 0]
        """
        if n <= 0:
            return a.parent().Zero

        res = a.bell_polynomials(1)
        for k in range(2, n + 1):
            res += a.bell_polynomials(k)
        return res

    def genfunc(a, n):
        """
        Returns the generating function of this powerseries up to term
        a[n-1]*x**(n-1).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: f = P.by_list([1,2,3],-2).polynomial(5)                  
        sage: g = P.by_list([1,2,3],-2).genfunc(5)
        sage: f(3.7r)==g(3.7r)
        True
        """
        m = a.min_index
        return lambda x: sum([a[k] * x ** k for k in range(m, n)], a.K0)

    def powerseries(a, n, name='x', R=None):
        if R is None:
            R = a.K
        m = a.min_index
        Q = PowerSeriesRing(R, name=name, default_prec=n)
        if m >= 0:
            return Q(a[:n])
        xp = Q.gen()
        return Q(a[m:n]) / Q(xp ** (-m))

    def polynomial(a, n, name='x', R=None):
        """
        Returns the associated polynomial for the first n coefficients.
        You can specify a different Ring with R, it tries to convert to.
        f_0 + f_1*x + f_2*x^2 + ... + f_{n-1}*x^{n-1}

        In case of a Laurant series with e.g. min_index=-2:
        f_{-2} x^(-2) + f_{-1} x^(-1) + ... + f_{n-1}*x^{n-1}
        
        You can adjust the variable by setting x.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.by_list([0,1,2]).polynomial(5).padded_list()
        [0, 1, 2]
        sage: P.Exp.polynomial(5,'y')
        1/24*y^4 + 1/6*y^3 + 1/2*y^2 + y + 1
        sage: (1/P.Dec_exp).polynomial(5,'y')
        (-1/720*y^4 + 1/12*y^2 - 1/2*y + 1)/y
        """

        #        return PolynomialRing(a.K,x)(sum([a[k]*x**k for k in range(n)],a.K0))
        if R is None:
            R = a.K
        m = a.min_index
        if m >= 0:
            P = PolynomialRing(R, name)
            return P(a[:n])

        Q = PolynomialRing(R, name)
        xp = Q.gen()
        return Q(a[m:n]) / Q(xp ** (-m))

    def mittag_leffler_polynomial(self, n):
        """
        Returns the Mittag-Leffler polynomial which has degree
        n^2 + n^4 + ... + n^(2n).
        The sequence of Mittag-Leffler polynomials converges inside 
        the Mittag-Leffler star to the continuation of the powerseries to it.
        """

        P = PolynomialRing(QQ, 'x')

        mlpc = self.parent().mlpc

        # index k from 1 to n
        def s(k, n):
            if (k, n) in mlpc:
                return mlpc[(k, n)]

            if k == 0:
                return P.one_element()
            S = s(k - 1, n)
            R = P.zero_element()
            for mk in range(n ** (2 * k) + 1):
                R += S.shift(mk) / Integer(factorial(mk))
            # print k,R
            mlpc[(k, n)] = R
            return R

        coeffs = s(n, n).coefficients()
        for N in range(len(coeffs)):
            coeffs[N] *= self[N] * factorial(N) / n ** N

        return PolynomialRing(self.K, 'x')(coeffs)

    #     def subs(a,*args,**kwargs):
    #         def f(n):
    #             if n < a.min_index:
    #                 return 0
    #             if a[n] == 0:
    #                 return 0
    #             if a[n] == 1:
    #                 return 1
    #             return a[n].subs(*args,**kwargs)
    #         return FormalPowerSeries(f,a.min_index)

    def _assertp0(a):
        """
        Asserts a[0]==0.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,2])._assertp0()
        """
        assert a.min_index > 0, "min_index must be > 0, but is " + repr(a.min_index) + ". Use reclass() if necessary."

    def _repr_(a):
        """
        Returns a string representation of a, as list of the first
        coefficients.
        If it is a formal Laurant series 
        the coefficients before index 0 are seperated by ";"

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ).by_list([1,2,3],-2)
        [1, 2; 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: FormalPowerSeriesRing(QQ).by_list([1,2,3],2) 
        [0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: FormalPowerSeriesRing(QQ).by_list([1,2,3],-2)._repr_()
        '[1, 2; 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]'
        """
        #         res = ""
        #         for n in range(80):
        #             coeff = a(n)
        #             s = ""
        #             if coeff != 0:
        #                 if coeff != 1:
        #                     s += repr(a(n)) + "*"
        #                 if n != 0:
        #                     s += "x"
        #                     if n != 1:
        #                         s += "^" + repr(n)
        #                 else:
        #                     s += repr(a(n))
        #                 s += " + "
        #             if len(res)+len(s) > 75: break
        #             else: res += s

        #         res += "O(x^" + repr(n) + ")"
        if a.coeffs is None:
            return "Undefined"

        res = "["
        if a.min_index < 0:
            for k in range(a.min_index, 0):
                res += repr(a[k])
                if k == -1:
                    res += "; "
                else:
                    res += ", "
        for n in range(80):
            s = repr(a[n]) + ", "
            if len(res) + len(s) > 76:
                break
            else:
                res += s

        res += "...]"
        # res = repr([ a(m) for m in range(10)])
        return res

    def n(a, *args, **kwargs):
        """
        Applies n to the coefficients

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.n(digits=3)
        [1.00, 1.00, 0.500, 0.167, 0.0417, 0.00833, 0.00139, 0.000198, 0.0000248, ...]
        """
        return N(a, *args, **kwargs)

    def order(a):
        """
        Returns the first index i such that a[i] != 0
        Does not terminate if a == 0

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,0,42]).order()
        2
        sage: P.by_list([1],-42).order()
        -42
        """
        n = a.min_index
        while a[n] == 0:
            n += 1
        return n

    def __lshift__(a, m=1):
        """
        Returns the powerseries with coefficients shiftet to the left by m.
        The coefficients a[0],...,a[m-1] get lost.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing, mul_factorial
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P.Exp.apply(mul_factorial)
        sage: (p << 1) - p
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return Lshift(a, m)

    def __rshift__(a, m=1):
        """
        Returns the powerseries with coefficients shifted to the right by m.
        The resulting coefficients b[0],...,b[m-1] are zero.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing, mul_factorial
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P.Exp.apply(mul_factorial)
        sage: (p >> 1) - p
        [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return Rshift(a, m)

    def diff(a, m=1):
        """
        Differentiates the powerseries m times.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.diff(3) - P.Exp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.by_list([1],5).diff(5)[0] == factorial(5)
        True
        """
        return Diff(a, m)

    def integral(a, c=0):
        """
        Integrates the powerseries with integration constant c

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.integral(1) - P.Exp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Exp.integral(0) + P.One - P.Exp  
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        return Integral(a, c)

    def root_test(self):
        return self.parent().by_lambda(lambda n: 1 / abs(self[n]) ** (1 / Integer(n)) if n > 0 else 0)

    #     def indefinite_sum(f,c=0):
    #         def ids(n,m):
    #             N = m+1
    #             if n > N:
    #                 return 0
    #             if n < 0:
    #                 return 0
    #             if n == 0:
    #                 return c
    #             if n == N:
    #                 return 1/QQ(n)
    #             return - sum([ f[k]*binomial(k,n) for k in range(n+1,N+1)])/QQ(n)
    #         print ids(1,2), ids(2,2), ids(3,2)

    # # # finite approximate operations

    def l2(p, N):
        """
        l2 norm: computes sqrt(|p[0]|^2 + |p[1]|^2 + ... |p[N-1]|^2)
        """
        return sqrt(sum([abs(p[n]) ** 2 for n in range(N)]))

    def carleman_matrix(p, M, N=None):
        """
        The carleman_matrix has as nth row the coefficients of p^n.
        It has N rows and N columns, except M specifies a different number of 
        rows.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,1]).carleman_matrix(4) == matrix([[1,0,0,0],[1,1,0,0],[1,2,1,0],[1,3,3,1]])                      
        True
        """
        if N is None:
            N = M
        return matrix([[p.npow(m)[n] for n in range(N)] for m in range(M)])

    def bell_matrix(a, M, N=None):
        """
        The Bell matrix with N (or M) rows and N columns of this power series.
        The n-th column of the Bell matrix is the sequence of coefficients 
        of the n-th power of the power series.
        The Bell matrix is the transpose of the Carleman matrix.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,1]).bell_matrix(4) == matrix([[1,1,1,1],[0,1,2,3],[0,0,1,3],[0,0,0,1]])                      
        True
        """
        if N is None:
            N = M
        return matrix([[a.npow(n)[m] for n in range(N)] for m in range(M)])

    def abel_matrix(self, N, repl_col=None):
        """
        is the bell matrix - identity matrix with first column removed and square truncated.
        """

        res = self.bell_matrix(N, N + 1)[:, 1:N + 1] - identity_matrix(N + 1)[:N, 1:N + 1]
        if repl_col is None:
            return res
        res.set_column(repl_col, [1] + [0] * (N - 1))
        return res


class FormalPowerSeries0(FormalPowerSeries):
    """
    The formal powerseries f with f[0]==0.
    """
    #     def __init__(self,f=None,min_index=1,**kwargs):
    #         """
    #         Initializes this FormalPowerSeries0.
    #         Should be called only from FormalPowerSeriesRing.

    #         sage: None
    #         """
    #         assert min_index >= 1
    #         super(FormalPowerSeries0,self).__init__(f,min_index,**kwargs)

    is0 = True
    is01 = False

    def __init__(self, parent, **kwargs):
        FormalPowerSeries.__init__(self,parent,**kwargs)

    def set_parabolic(a, n):
        """
        Tells whether a[1]**n = 1
        """
        if a[1] ** n == a.K1:
            a.parabolic = n

    def __or__(a, b):
        """
        Composition (right after left): a|b.
        For documentation see: `compose'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,1,2]) | P([1,2,3])
        [1, 2, 7, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return b(a)

    def nit(a, n):
        """
        n times iteration (n times composition), n is a natural number.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(1/(x+1)-1,x).nit(2)
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        _assert_nat(n)

        if n == 0:
            return a.parent().Id
        if n == 1:
            return a
        if n not in a._itMemo:
            n1 = n // 2
            n2 = n // 2 + n % 2
            a._itMemo[n] = a.nit(n1).compose(a.nit(n2))
        return a._itMemo[n]

    def it(a, t):
        """
        The t-th (possibly non-integer) iteration.

        It satisfies:
        a.it(0) = Id
        a.it(1) = a
        a.it(s+t) == a.it(s)(a.it(t))

        See also: nit, regit (for restrictions depending t's kind)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,2]).it(-2)              
        [0, 1/4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p = P([0,2]).regit_b(1/2)
        sage: (p[0],p[1],p[2])
        (0, sqrt(2), 0)
        """
        a._assertp0()

        if isinstance(t, Integer) or isinstance(t, int):
            if t >= 0:
                return a.nit(t)
            return a.inv().nit(-t)
        return a.regit(t)

    def regit(a, t, is_pow=False):
        """
        Regular (non-integer) iteration (works also for integer t).
        Preconditions: 
            a[1]**n != a[1] for all n. 
            Particularly a[1]!=0 and a[1]!=1.
            a[1]**t must be defined.

        is_pow=True means that t is not the exponent but the whole power (a_1)^t

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,2]).regit(1/2)[:3]
        [0, sqrt(2), 0]

        sage: PQ = PolynomialRing(QQ,'z,zt')
        sage: z,zt = PQ.gens()
        sage: FPQ = FormalPowerSeriesRing(PQ)
        sage: p = FPQ([0,z,3*z])
        sage: p.regit(zt,is_pow=True)[1]
        zt
        sage: p.regit(zt,is_pow=True)[3] - (-18*z*zt^2 + 18*zt^3 + 18*z*zt - 18*zt^2)/(z^3 - z^2 - z + 1)
        0
        """

        a._assertp0()

        return Regit_hyp(a, t, is_pow)

    def regit_b(a, t):
        """
        Regular iteration via the schroeder function.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([0,2])
        sage: p.regit_b(1/2)[0:3]
        [0, sqrt(2), 0]
        """
        s = a.schroeder()
        return s.inv()(s.smul(a[1] ** t))

    def inv(a):
        """
        The inverse.

        Precondition: a[1] != 0
        Satisfies: a.inv()(a)=Id
        Alternative expression: a.inv() == ~a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Xexp.inv() - P.Lambert_w   
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: ~P.Inv_selfroot_inc.dec().reclass() - P.Selfroot_inc.dec() 
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        a._assertp0()

        return Inv(a)

    inverse = inv

    __invert__ = inv

    #     def julia_b(a):
    #         """
    #         diff(it(a,t),t)(t=0) == ln(a[1])*julia(a)
    #         """
    #         a._assertp0()

    #         Poly=PolynomialRing(a.K,'x')
    #         b = FormalPowerSeriesRing(Poly)()
    #         b.min_index = 1

    #         def f(n):
    #             """ sage: None   # indirect doctest """
    #             if decidable0(a.K):
    #                 assert a[1] != 0

    #             if n == 0:
    #                 return Poly([0])
    #             if n == 1:
    #                 return Poly([0,1])
    #             res = a[n]*(b[1]**n)-b[1]*a[n]
    #             res += sum([a[m]*b.npow(m)[n] - b[m]*a.npow(m)[n] for m in range(2,n)],a.K0)
    #             res /= a[1]**n - a[1]
    #             return res
    #         b.coeffs = f

    #         def h(p):
    #             """ sage: None # indirect doctest """
    #             return sum([p.coeffs()[n]*n for n in range(p.degree()+1)],a.K0)

    #         return a.new(lambda n: h(b[n]))

    def expit(a,a1=None):
        """
        The inverse Operator of logit. I.e. given a function j we want to retrieve the function f
        such that
        j o f = f' * j

        sage: PQ = FormalPowerSeriesRing(QQ)
        sage: p = PQ([0,1,0,2])
        sage: p.logit().expit() - p
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p = PQ.Dec_exp
        sage: p.logit().expit() - p
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return Expit01(a, a1=a1)

    def logit(a):
        """
        Iterative logarithm (a[0]==0 and 
        a[1]==1 or a[1] not being a primitive root of unit required).

        It has different equivalent definitions:
        1. j = diff(a.it(t),t)(t=0)
        2. Solution j of Julia equation j o a = a' * j, with j[1]==log(a[1]) 
           and in the case a[1]==1 additionally:
            j[0]=...=j[m]=0, j[m+1]=a[m+1], m = valit(a)

        It starts with  (As the Julia equation
        is also satisfied by c*j for any constant c the additional
        condition in 2, where j[1]=0, is necessary to determine j.)

        It has similar properties like the logarithm:
        logit(f^t) == t*logit(f)

        It can be used to define the regular Abel function abel(f) by
        abel(f)' = 1/logit(f)

        Refs:
        Eri Jabotinsky, Analytic iteration (1963), p 464
        Jean Ecalle, Theorie des Invariants Holomorphes (1974), p 19
        Marek Kuczma, Iterative functional equations, 8.5A

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing

        #The case a not being a primitive root of unit, e.g. |a[1]|!=1
        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P([0,2,0,1])
        sage: j = a.logit()                   
        sage: j(a) - a.diff()*j            
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P = FormalPowerSeriesRing(SR)
        sage: a = P([0,2,1])
        sage: j = a.logit()
        sage: t = var('t')
        sage: ait = a.it(t)
        sage: [j[n] - diff(ait[n],t)(t=0) for n in range(10)]
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

        #The case a[1]==1
        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P([0,1,0,2])
        sage: vector(a.logit()[:10]) - vector(a.logit_jabotinsky()[:10])
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P.Dec_exp
        sage: j = a.logit()
        sage: j(P.Dec_exp) - P.Dec_exp.diff() * j
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P = FormalPowerSeriesRing(SR)
        sage: de = P.Dec_exp
        sage: j = de.logit()
        sage: t = var('t')
        sage: ait = de.it(t)
        sage: [j[n] - diff(ait[n],t)(t=0) for n in range(15)]
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

        """
        return a.julia(scale=log(a[1]))

    def julia(a, scale=1):
        """
        The Julia function of a.
        
        It is the same as logit() except that j[1]=scale in the case a[1]!=1 
        It can be used instead of logit() to avoid introducing logarithms 
        into the coefficients. 
        E.g. if you work in a polynomial ring for the coefficients.


        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P([0,2,1])               
        sage: j = a.julia()                   
        sage: j(a) - a.diff()*j            
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        if a[1] == a.K1:
            return Logit01(a, scale)
        return Logit_hyp(a, scale)

    #     def logit(a):
    #         """
    #         """

    #         #TODO this should be possible directly
    #         _t = var('_t')
    #         g = a.it(_t)
    #         def f(n):
    #             """ sage: None   # indirect doctest """
    #             return diff(g[n],_t)(_t=0)
    #         res = a.new(f)
    #         res.min_index = res.order()
    #         return res

    def schroeder(a):
        """
        Returns the Schroeder powerseries s with s[1]=1
        for a powerseries a with a[0]=0 and a[1]^n!=a[1] for all n

        The Schroeder powerseries s is determined up to a multiplicative
        constant by the functional equation:
        s(a(z))=a[1]*s(z)

        Let f(x) = 2*x + x**2, let s(x)=log(1+x), then s(f(x))=2*s(x):
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,2,1]).schroeder() - P.Log_inc
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        a._assertp0()

        return Schroeder(a)

    def inv_schroeder(a):
        """
        Returns the inverse Schroeder powerseries.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([0,2,3])               
        sage: p.inv_schroeder() | p.schroeder()
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return InvSchroeder(a)

    def abel_coeffs(f):
        """
        The regular Abel function of a powerseries f (f[1]**n != f[1])
        has the form r*ln(x)+ps(x) where ps is a powerseries.

        This method returns [r,ps].
        """
        return [1 / log(f[1]), f.abel().smul(1 / log(f[1]))]

    def abel(f):
        """
        The regular Abel function of a powerseries f (f[1]**n != f[1]) 
        has the form a(x)=(ln(x)+ps(x))/ln(f[1])
        where ps is a powerseries
        
        This method returns ps.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing,FormalPowerSeries0
        sage: a = var('a')
        sage: p = FormalPowerSeriesRing(PolynomialRing(QQ,a))(exp(a*x)-1,x)
        sage: pah = p.abel()
        sage: pac = p.abel2()
        sage: pah
        [0, -1/2*a/(a - 1), (5/24*a^3 + 1/24*a^2)/(a^3 - a^2 - a + 1), ...]
        sage: [pac[k] - pah[k]==0 for k in range(0,5)]
        [True, True, True, True, True]
        """
        f._assertp0()

        P = f.parent()
        return (f.schroeder() << 1).dec().reclass() | P.Log_inc

    def abel2(a):
        """
        A different implementation of abel(f) via
        integration of 1/julia(a).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing, FormalPowerSeries0
        sage: a = var('a')
        sage: p = FormalPowerSeriesRing(PolynomialRing(QQ,a))(exp(a*x)-1,x)
        sage: p.abel2()
        [0, -1/2*a/(a - 1), (5/24*a^3 + 1/24*a^2)/(a^3 - a^2 - a + 1), ...]
        
        """

        return a.julia().rcp().extinct_before(0).integral()

    def valit(a):
        """
        Returns the last index i such that a[i] == Id[i].

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,1,0,0,1]).valit()
        3
        """
        assert a[0] == 0, a[0]

        if not a[1] == 1:
            return 0

        n = 2
        while a[n] == 0:
            n += 1

        return n - 1


class FormalPowerSeries01(FormalPowerSeries0):
    """
    The FormalPowerSeriess p with p[0]==0 and p[1]==1.
    """

    #     def it_b(p,t):
    #         """
    #         A different direct implementation for `it'.

    #         sage: p = P.Dec_exp.it_b(1/2)
    #         sage: (p | p) - P.Dec_exp
    #         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
    #         """
    #         N=p.valit()
    #         P = p.parent()
    #         q = P()
    #         def f(n):
    #             """ sage: None   # indirect doctest """
    #             if n < N:
    #                 return P.Id[n]
    #             if n == N:
    #                 return t * p[N]
    #             if n > N:
    #                 r=p[n]
    #                 r+=sum([p[m]*(q**m)[n] - q[m]*(p**m)[n] for m in range(N,n)])
    #                 return r

    #         q.coeffs = f
    #         return q

    is01 = True

    def __init__(self, parent, **kwargs):
        FormalPowerSeries0.__init__(self,parent,**kwargs)
        # TODO: assert
        self.min_index = 1

    def regit(a, t, k=0, a1=None, avp1=None, a0tovp1=None):
        """
        Regular iteration for powerseries with a[0]==0 and a[1]==1. 
        The iteration index t needs not to be an integer.
        t should be a number in the base ring of this powerseries, 
        but at least have a defined multiplication with the elements 
        of the base ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P.Dec_exp.regit(1/2)  
        sage: (p | p) - P.Dec_exp    
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: h = P([0,-1,0,0,1,1])
        sage: f = h(h).reclass()
        sage: f.valit()
        4
        sage: g0 = f.regit(1/4,a1=1)
        sage: g1 = f.regit(1/4,a1=I)
        sage: g2 = f.regit(1/4,a1=-1)
        sage: g3 = f.regit(1/4,a1=-I)
        sage: g0.nit(4) - f
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: g1.nit(4) - f
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: g2.nit(4) - f
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: g3.nit(4) - f
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: f.regit(1/2,a1=-1) - h
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        return Regit01(a, t, k=k, a1=a1, avp1=avp1, a0tovp1=a0tovp1)

    def itop(a, ie):
        """
        Regular iteration as operation of two FormalPowerSeries.
        The iteration exponent ie is a FormalPowerSeries. 
        The result is again a FormalPowerSeries01.
        
        Alternative expression: a.it(t) == a & t

        Requires a[0]==0 and a[1]==0.
        """

        return a.regit(ie).crush()

    __and__ = itop

    def logit_jabotinsky(a):
        """
        Iterative logarithm for the case a[0]==0 and a[1]==1.
        Following an early method of Jabotinsky.
        It is considered to be quite slow but maybe used for comparison.


        It satisfies j := logit(a) = diff(a.it(t),t)(t=0)
        and it is also the solution of j of 
        j o a = a' * j, j[0]=...=j[valit(a)]=0, j[valit(a)+1]=a[valit(a)+1]

        It can be used to obtain the regular Abel function abel(f) by
        abel(f)' = 1/logit(f)

        It has similar properties like the logarithm:
        logit(f^t) == t*logit(f)

        Refs:
        Eri Jabotinsky, Analytic iteration (1963), p 464
        Jean Ecalle, Theorie des Invariants Holomorphes (1974), p 19
        Marek Kuczma, Iterative functional equations, 8.5A

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: j = P.Dec_exp.logit_jabotinsky()
        sage: j(P.Dec_exp) - P.Dec_exp.diff() * j
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: P = FormalPowerSeriesRing(SR)
        sage: de = P.Dec_exp
        sage: j = de.logit_jabotinsky()
        sage: t = var('t')
        sage: ait = de.it(t)
        sage: [j[n] - diff(ait[n],t)(t=0) for n in range(15)]
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        """

        return Logit_Jabotinsky(a)

    def abel_coeffs(a):
        """
        The Abel function a of a power series f with f[0]=0 and f[1]=1
        generally has the form
        F(z) + p(z), where
        F(z)=ji[-m]*z^{-m+1}/(-m+1)+...+ji[-2]*z^{-1}/(-1)+ji[-1]*log(z)
        and p is a powerseries (with positive indices only)

        ji[-1] is called the iterative residue (Ecalle)
        ji is the reciprocal of the iterative logarithm
        -which is meromorphic- of f

        The method returns the sequence [ji[-1],[F[-m+1],...,F[-1],p[0],p[1],p[2],...]

        These coefficients can be useful to compute the Abel function, 
        for which the powerseries is a non-converging asymptotic development.

        The Abel function can then be gained by
        lim_{n->oo} F(f&n(z))-n

        
        sage: from sage.rings.formal_powerseries import *
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,1,0,2]).abel_coeffs()
        [3/2, [-1/4, 0; 0, 0, -5/4, 0, 21/8, 0, -35/4, 0, 2717/80, 0, -13429/100, 0, ...]]
        sage: p = P([0,1,0,0,1,2,3])
        sage: a = p.abel_coeffs()
        sage: a
        [6, [-1/3, 1, -1; 0, -10, 11/2, 17/9, -169/12, 349/30, 13/18, -544/21, 1727/24, ...]]
        sage: ((p << 1).log().smul(a[0]) + (p | a[1]) - a[1]).reclass()
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        juli = a.logit().rcp()
        #         m = jul.order()
        #         juli = (jul << m).rcp()
        #         return [[ juli[m+i]/(i+1) for i in range(-m,-1) ],juli[m-1], (juli<<m).integral()]
        resit = juli[-1]
        # juli[-1]=0
        return [resit, juli.set_item(-1, 0).integral()]


# # # Constructors # # #

class Constant(FormalPowerSeries):
    def __init__(self, parent, c):
        """
        Description and tests at FormalPowerSeriesRing.by_constant
        sage: None   # indirect doctest
        """
        FormalPowerSeries.__init__(self, parent)
        self.c = parent.K(c)

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.c
        return self.K0


class Iterated(FormalPowerSeries):
    def __init__(self, parent, g, min_index):
        """
        Description and tests at FormalPowerSeriesRing.by_generator
        sage: None   # indirect doctest
        """
        FormalPowerSeries.__init__(self, parent, min_index=min_index)
        self.g = g

    def coeffs(self, n):
        """ sage: None # indirect doctest """
        g = self.g

        if n < self.min_index:
            return self.K0
        if n == self.min_index:
            return next(g)
        x = self[n - 1]  # dummy to compute the prev value
        return next(g)


class List(FormalPowerSeries):
    def __init__(self, parent, the_list, start):
        """
        Description and tests at FormalPowerSeriesRing.by_list
        sage: None   # indirect doctest
        """
        FormalPowerSeries.__init__(self, parent)

        L = len(the_list)
        M = 0
        for M in range(L):
            if the_list[M] != 0:
                break
        N = -1
        for i in range(L):
            N = L - i - 1
            if the_list[N] != 0:
                break

        self.min_index = start + M
        self.max_index = start + N
        self.start = start
        self.list = the_list

    def coeffs(self, k):
        """ sage: None   # indirect doctest """
        if k < self.min_index or k > self.max_index:
            return self.K0
        return self.list[k - self.start]


class Taylor(FormalPowerSeries):
    def __init__(self, parent, expr, v, at):
        """
        Description and tests at FormalPowerSeriesRing.by_taylor
        sage: None   # indirect doctest
        """
        assert v is not None
        assert isinstance(v, Expression)  # this should be Variable

        si = FormalPowerSeries.__init__
        # coeffs always returns non-empty list, at least [0,0] is contained
        min_index = expr.taylor(v, at, 2).substitute({v: v + at}).coefficients(v)[0][1]
        si(self, parent, min_index=min_index)

        self.expr = expr
        self.v = v
        self.at = at

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        # too slow
        # if not at == 0 and n==0:
        #    return expr({v:at})-at
        # return simplify(diff(expr,v,n).substitute({v:at})/factorial(n))
        expr = self.expr
        v = self.v
        at = self.at
        return self.K(expr.taylor(v, at, n).substitute({v: v + at}).coefficient(v, n))


# # # Constants # # #

class Zero(FormalPowerSeries0):
    """
    The zero element power series.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Zero))
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
    """
    hint = HintType([0, 0])

    def __init__(self, parent):
        FormalPowerSeries.__init__(self, parent, min_index=2)

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        return self.K0


class One(FormalPowerSeries):
    """
    The one element power series.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.One)) 
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
    """
    hint = HintType([1, 0])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K1
        return self.K0


class Id(FormalPowerSeries01):
    """
    The powerseries of the identity function id(x)=x.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Id)) 
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 1:
            return self.K1
        return self.K0


class Inc(FormalPowerSeries):
    """
    The powerseries of the increment function inc(x)=x+1.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Inc))
    [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0 or n == 1:
            return self.K1
        return self.K0


class Dec(FormalPowerSeries):
    """
    The powerseries of the decrement function dec(x)=x-1.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Dec))                                            
    [-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
    """
    hint = HintType([-1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return -self.K1
        if n == 1:
            return self.K1
        return self.K0


class Exp(FormalPowerSeries):
    """
    The powerseries of the exponential function.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Exp))
    [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K1
        return self[n - 1] / n


class Dec_exp(FormalPowerSeries01):
    """
    The powerseries of the decremented exponential dec_exp(x)=exp(x)-1.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Dec_exp))      
    [0, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K0
        if n == 1:
            return self.K1
        return self[n - 1] / n


class Log_inc(FormalPowerSeries01):
    """
    The powerseries of the logarithm at 1 
    or the powerseries of f(x)=log(x+1) at 0.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Log_inc))
    [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K0
        return self.K((-1) ** (n + 1) / Integer(n))


class Sin(FormalPowerSeries01):
    """
    The powerseries of the sine.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Sin))
    [0, 1, 0, -1/6, 0, 1/120, 0, -1/5040, 0, 1/362880, 0, -1/39916800, 0, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 0:
            return self.K0
        if n == 1:
            return self.K1
        return self[n - 2] / (-n * (n - 1))


class Cos(FormalPowerSeries):
    """
    The powerseries of the cosine.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Cos))
    [1, 0, -1/2, 0, 1/24, 0, -1/720, 0, 1/40320, 0, -1/3628800, 0, 1/479001600, ...]
    """
    hint = HintType([1, 0])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 1:
            return self.K0
        if n == 0:
            return self.K1
        return self[n - 2] / (-n * (n - 1))


class Arcsin(FormalPowerSeries01):
    """
    The powerseries of arcsin.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Arcsin))
    [0, 1, 0, 1/6, 0, 3/40, 0, 5/112, 0, 35/1152, 0, 63/2816, 0, 231/13312, 0, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """

        if n % 2 == 0:
            return self.K0

        if n == 1:
            return self.K1

        return self[n - 2] * (n - 2) * (n - 2) / (n - 1) / n


class Arctan(FormalPowerSeries01):
    """
    The powerseries of arctan.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Arctan))
    [0, 1, 0, -1/3, 0, 1/5, 0, -1/7, 0, 1/9, 0, -1/11, 0, 1/13, 0, -1/15, 0, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 0:
            return self.K0
        return self.K((-1) ** (n // 2) / Integer(n))


class Sinh(FormalPowerSeries01):
    """
    The powerseries of sinh.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Sinh))
    [0, 1, 0, 1/6, 0, 1/120, 0, 1/5040, 0, 1/362880, 0, 1/39916800, 0, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 0:
            return self.K0
        if n == 1:
            return self.K1
        return self[n - 2] / (n * (n - 1))


class Cosh(FormalPowerSeries):
    """
    The powerseries of cosh.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Cosh))
    [1, 0, 1/2, 0, 1/24, 0, 1/720, 0, 1/40320, 0, 1/3628800, 0, 1/479001600, 0, ...]
    """
    hint = HintType([1, 0])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 1:
            return self.K0
        if n == 0:
            return self.K1
        return self[n - 2] / (n * (n - 1))


class Arcsinh(FormalPowerSeries01):
    """
    The powerseries of arcsinh.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Arcsinh))
    [0, 1, 0, -1/6, 0, 3/40, 0, -5/112, 0, 35/1152, 0, -63/2816, 0, 231/13312, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 0:
            return self.K0
        if n == 1:
            return self.K1

        return -self[n - 2] * (n - 2) * (n - 2) / (n - 1) / n


class Arctanh(FormalPowerSeries01):
    """
    The powerseries of arctanh.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Arctanh))
    [0, 1, 0, 1/3, 0, 1/5, 0, 1/7, 0, 1/9, 0, 1/11, 0, 1/13, 0, 1/15, 0, 1/17, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n % 2 == 0:
            return self.K0
        return self.K1 / n


class Tan(FormalPowerSeries01):
    """
    The powerseries of tan.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: P.Tan
    [0, 1, 0, 1/3, 0, 2/15, 0, 17/315, 0, 62/2835, 0, 1382/155925, 0, ...]
    """
    hint = HintType([0, 1])

    def __init__(self, parent):
        super().__init__(parent)

    def coeffs(self, N):
        """ sage: None   # indirect doctest """
        if N % 2 == 0:
            return self.K0
        n = (N + 1) // 2
        P = self.parent()
        return self.K(P.Bernoulli[2 * n] * (-4) ** n * (1 - 4 ** n) / factorial(2 * n))


class Tanh(FormalPowerSeries01):
    """
    The powerseries of tanh.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: P.Tanh
    [0, 1, 0, -1/3, 0, 2/15, 0, -17/315, 0, 62/2835, 0, -1382/155925, 0, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, N):
        """ sage: None   # indirect doctest """
        if N % 2 == 0:
            return self.K0
        n = (N + 1) // 2
        P = self.parent()
        return self.K(P.Bernoulli[2 * n] * (-1) ** (2 * n) * 4 ** n * (4 ** n - 1) / factorial(2 * n))


class Xexp(FormalPowerSeries01):
    """
    The powerseries of x*exp(x)

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Xexp))   
    [0, 1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K0
        if n == 1:
            return self.K1
        return self[n - 1] / (n - 1)


class Lambert_w(FormalPowerSeries01):
    """
    The Lambert W function is the inverse of f(x)=x*e^x 

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Lambert_w))
    [0, 1, -1, 3/2, -8/3, 125/24, -54/5, 16807/720, -16384/315, 531441/4480, ...]
    """
    hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K0
        if n == 1:
            return self.K1
        return self.K((-n) ** (n - 1)) / self.K(factorial(n))


class Sqrt_inc(FormalPowerSeries):
    """
    The powerseries of sqrt at 1, or of sqrt(x+1) at 0.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Sqrt_inc))
    [1, 1/2, -1/8, 1/16, -5/128, 7/256, -21/1024, 33/2048, -429/32768, ...]
    """
    hint = HintType([1, 1 / Integer(2)])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.K1
        return -self[n - 1] * (2 * n - 3) / (2 * n)


# class BernoulliVar(FormalPowerSeries):
#     """
#     The variant of the Bernoulli numbers where B[1]=1/2
#     instead of B[1]=-1/2
#     """
#     def coeffs(self,n):
#         if n == 1:
#             return self.K(1)/self.K(2)
#         return self.Bernoulli[n]

# class Faulhaber(FormalPowerSeries):
#     """
#     Faulhaber's formula.
#     """
#   def coeffs(self,n):


class Stirling1(FormalPowerSeries):
    """
    Returns the sequence of Stirling numbers of the first kind.
    These are the coefficients of the polynomial x(x-1)(x-2)...(x-n+1).
    stirling1[n][k] is the coefficient of x^k in the above polynomial.
    """

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        P = self.parent()
        if n == 0:
            return P.One

        res = Stirling1_Succ(P, self[n - 1], n)
        return res


class Stirling1_Succ(FormalPowerSeries):
    """
    Constructs the sequence of Stirling numbers stirling1[n]
    from g = stirling1[n-1]
    """

    def __init__(self, parent, g, n):
        """ sage: None   # indirect doctest """
        FormalPowerSeries.__init__(self, parent, min_index=1)
        self.g = g
        self.n = n

    def coeffs(self, k):
        """ sage: None   # indirect doctest """
        g = self.g
        n = self.n
        return g[k - 1] - (n - 1) * g[k]


class Lehmer_comtet(FormalPowerSeries):
    """
    The n-th Lehmer-Comtet number is the n-th derivative of x^x at 1.
    See Sloane A008296.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.Lehmer_comtet))
    [1, 1, 3, 10, 41, 196, 1057, 6322, 41393, 293608, 2237921, 18210094, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        return self.K(sum([k ** (n - k) * binomial(n, k) for k in range(n + 1)]))


class Selfpower_inc(FormalPowerSeries):
    """
    The powerseries of x^x at 1.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: P.Selfpower_inc
    [1, 1, 1, 1/2, 1/3, 1/12, 3/40, -1/120, 59/2520, -71/5040, 131/10080, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        P = self.parent()
        return self.K(sum([P.Stirling1[n][k] * P.A000248[k] for k in range(n + 1)])) / factorial(n)


class Superroot_inc(FormalPowerSeries):
    """
    The powerseries of the inverse of x^x developed at 1.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: P.Superroot_inc
    [1, 1, -1, 3/2, -17/6, 37/6, -1759/120, 13279/360, -97283/1008, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        P = self.parent()
        return self.K(sum([P.Stirling1[n][k] * Integer(1 - k) ** (k - 1) for k in range(n + 1)])) / factorial(n)


class A003725(FormalPowerSeries):
    """
    The derivatives of exp(x*e^(-x)) at 0.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: loads(dumps(P.A003725))
    [1, 1, -1, -2, 9, -4, -95, 414, 49, -10088, 55521, -13870, -2024759, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        return self.K(sum([(-k) ** (n - k) * binomial(n, k) for k in range(n + 1)]))


class Selfroot_inc(FormalPowerSeries):
    """
    The powerseries of x^(1/x) at 1.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: P.Selfroot_inc
    [1, 1, -1, 1/2, 1/6, -3/4, 131/120, -9/8, 1087/1260, -271/720, -2291/10080, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        P = self.parent()
        return self.K(sum([P.Stirling1[n][k] * P.A003725[k] for k in range(n + 1)])) / factorial(n)


class Inv_selfroot_inc(FormalPowerSeries):
    """
    The inverse of the self root x^(1/x) at 1.
    The inverse of the self root for x=b is the fixed point of f(y)=b^y.

    sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
    sage: P = FormalPowerSeriesRing(QQ)
    sage: P.Inv_selfroot_inc
    [1, 1, 1, 3/2, 7/3, 4, 283/40, 4681/360, 123101/5040, 118001/2520, ...]
    """
    hint = HintType([1, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        P = self.parent()
        if n < 0:
            return self.K0
        if n == 0:
            return self.K1
        r = 0
        for k in range(1, n + 1):
            r += P.Stirling1[n][k] * P.K((k + 1)) ** (k - 1)

        return self.K(r) / factorial(n)


# # # Methods # # #

class ExtinctBefore(FormalPowerSeries):
    def __init__(self, a, min_index):
        """
        Description and tests at FormalPowerSeries.extinct_before
        sage: None   # indirect doctest
        """
        FormalPowerSeries.extinct_before.__doc__

        si = FormalPowerSeries.__init__
        si(self, a.parent())
        self.a = a
        self.min_index = min_index

        if hasattr(a, 'hint'):
            if min_index <= 1:
                self.hint = a.hint
            if min_index == 1:
                self.hint = HintType([0, a.hint[1]])
            if min_index >= 2:
                self.hint = HintType([0, 0])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n < self.min_index:
            return self.K0
        return self.a[n]


class Apply(FormalPowerSeries):
    def __init__(self, a, f, first=None, last=None, result_type=None, result_base_ring=None):
        """
        Description and tests at FormalPowerSeries.apply
        sage: None  # indirect doctest
        """
        if result_base_ring is not None:
            result_type = FormalPowerSeriesRing(result_base_ring)
        if result_type is None:
            result_type = a.parent()
        FormalPowerSeries.__init__(self, result_type, min_index=a.min_index)
        self.a = a
        self.f = f
        self.first = first
        self.last = last
        if hasattr(a, 'hint') and first is not None and first >= 2:
            self.hint = a.hint

    def coeffs(self, n):
        """ sage: None # indirect doctest """

        outside = False
        if self.first is not None and n < self.first:
            outside = True
        elif self.last is not None and n > self.last:
            outside = True
        if outside:
            return self.a[n]
        return self.f(self.a[n], n)


class IncMethod(FormalPowerSeries):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.inc
        sage: None   # indirect doctest
        """
        FormalPowerSeries.__init__(self, a.parent())
        self.a = a
        if hasattr(a, 'hint'):
            self.hint = a.hint + 1

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.a[0] + self.K1
        return self.a[n]


class DecMethod(FormalPowerSeries):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.dec
        sage: None   # indirect doctest
        """
        FormalPowerSeries.__init__(self, a.parent())
        self.a = a
        if hasattr(a, 'hint'):
            self.hint = a.hint - 1

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        if n == 0:
            return self.a[0] - self.K1
        return self.a[n]


class SMul(FormalPowerSeries):
    def __init__(self, a, s):
        """
        Description and tests at FormalPowerSeries.rmul
        sage: None   # indirect doctest
        """
        FormalPowerSeries.__init__(self, a.parent(), min_index=a.min_index)
        self.a = a
        self.s = s

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        return self.a[n] * self.s


class Add(FormalPowerSeries):
    def __init__(self, a, b):
        """
        Description and tests at FormalPowerSeries.add
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=min(a.min_index, b.min_index))
        self.a = a
        self.b = b
        if hasattr(a, 'hint') and hasattr(b, 'hint'):
            self.hint = a.hint + b.hint

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        b = self.b
        if n < a.min_index:
            if n < b.min_index:
                return self.K0
            return b[n]
        if n < b.min_index:
            return a[n]
        return a[n] + b[n]


class Sub(FormalPowerSeries):
    def __init__(self, a, b):
        """
        Description and tests at FormalPowerSeries.sub
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=min(a.min_index, b.min_index))
        self.a = a
        self.b = b
        if hasattr(a, 'hint') and hasattr(b, 'hint'):
            self.hint = a.hint - b.hint

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        b = self.b
        if n < a.min_index:
            if n < b.min_index:
                return self.K0
            # a[0]==0
            return -b[n]
        if n < b.min_index:
            # b[0]==0
            return a[n]
        return a[n] - b[n]


class Neg(FormalPowerSeries):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.neg
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=a.min_index)
        self.a = a
        if hasattr(a, 'hint'):
            self.hint = -a.hint

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        if n < a.min_index:
            return self.K0
        return -a[n]


class Mul(FormalPowerSeries):
    def __init__(self, a, b):
        """
        Description and tests at FormalPowerSeries.mul
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=a.min_index + b.min_index)
        self.a, self.b = a, b
        if hasattr(a, 'hint') and hasattr(b, 'hint'):
            self.hint = a.hint * b.hint

    def ab(self, m, n):
        """
        Lazy product of a[m] and b[n]
        sage: None # indirect doctest
        """
        a = self.a
        b = self.b
        if a[m] == 0:
            return self.K0
        return a[m] * b[n]

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a, b = self.a, self.b
        return sum([self.ab(k, n - k) for k in range(a.min_index, n + 1 - b.min_index)], self.K0)


class Div(FormalPowerSeries):
    def __init__(self, c, b):
        """
        Description and tests at FormalPowerSeries.div
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, c.parent(), min_index=c.min_index - b.min_index)
        self.c = c
        self.b = b

    def _ab(a, m, n):
        """
        Lazy product of b[n] and a[m].
        sage: None # indirect doctest
        """
        b = a.b
        if b[n] == 0:
            return a.K0
        return a[m] * b[n]

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self
        c = a.c
        b = a.b
        if n < a.min_index:
            return self.K0
        r = c[n + b.min_index]
        for k in range(a.min_index, n):
            r -= a._ab(k, n + b.min_index - k)
        return r / b[b.min_index]


class Npow(FormalPowerSeries):
    def __init__(self, f, m):
        """
        Description and tests at FormalPowerSeries.npow
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, f.parent(), min_index=f.min_index * m)
        self.f = f
        self.m = m
        if hasattr(f, 'hint'):
            self.hint = f.hint ** m

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        m = self.m
        if n < self.min_index:
            return self.K0
        return self.f._s(n - self.f.min_index * (m - 1), m, n)


class Nipow(FormalPowerSeries):
    def __init__(self, a, t):
        """
        Description and tests at FormalPowerSeries.nipow
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent())
        self.a = a
        self.t = t

    def coeffs(s, n):
        """ sage: None   # indirect doctest """
        a = s.a
        t = s.t
        if a.parent().is_decidable:
            assert a[0] != 0, "0th coefficient is " + repr(a[0]) + ", but must be non-zero for non-integer powers"

        da = a.set_item(0, s.K0)

        if n >= 0 and a[0] == 1:
            # dont use symbolic arithmetic for rational powers of 1
            return sum([binomial(t, k) * da.npow(k)[n] for k in range(n + 1)], s.K0)
        return sum([binomial(t, k) * a[0] ** t / a[0] ** k * da.npow(k)[n] for k in range(n + 1)], s.K0)


class Compose(FormalPowerSeries):
    def __init__(self, b, a):
        """
        Description and tests at FormalPowerSeries.compose
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, b.parent(), min_index=b.min_index * a.min_index)
        self.b = b
        self.a = a
        if hasattr(a, 'hint') and hasattr(b, 'hint'):
            self.hint = a.hint(b.hint)

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        b = self.b
        a = self.a
        res = sum([b[k] * (a.npow(k)[n]) for k in range(n + 1)], self.K0)
        if b.min_index < 0:
            bi = a.rcp()
            res += sum([b[k] * (bi.npow(-k)[n]) for k in range(b.min_index, 0)])
        return res


class Lshift(FormalPowerSeries):
    def __init__(self, a, m=1):
        """
        Description and tests at FormalPowerSeries.__lshift__
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent())
        self.a = a
        self.m = m

    def coeffs(self, n):
        """ sage: None # indirect doctest """
        return self.a[n + self.m]


class Rshift(FormalPowerSeries):
    def __init__(self, a, m=1):
        """
        Description and tests at FormalPowerSeries.__rshift__
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent())
        self.a = a
        self.m = m

    def coeffs(self, n):
        """ sage: None # indirect doctest """
        a = self.a
        m = self.m
        if n < m:
            return self.K0
        return a[n - m]


class Diff(FormalPowerSeries):
    def __init__(self, a, m=1):
        """
        Description and tests at FormalPowerSeries.diff
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=self.deg(a.min_index, m))
        self.a = a
        self.m = m
        if hasattr(a, 'hint'):
            self.hint = diff(a.hint, m)

    def deg(self, v, m):
        """ sage: None # indirect doctest """
        if v >= 0:
            return max(v - m, 0)
        return v - m

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        m = self.m
        if -m <= n and n < 0:
            return self.K0
        else:
            return a[n + m] * prod(k for k in range(n + 1, n + m + 1))


class Integral(FormalPowerSeries):
    def __init__(self, a, c=0):
        """
        Description and tests at FormalPowerSeries.integral
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        if c == 0:
            si(self, a.parent(), min_index=a.min_index + 1)
        else:
            si(self, a.parent())

        self.a = a
        self.c = c
        # if hasattr(a,'hint') and QQ.has_coerce_map_from(c.parent()):
        #     self.hint = integral(a.hint) + c

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        c = self.c

        if n == 0:
            return c
        if n < a.min_index + 1:
            return self.K0

        # This test can not be moved to the beginning because
        # it would break lazyness
        if a.min_index < 0:
            assert a[-1] == 0, "Coefficient at -1 must be 0, but it is: " + repr(a[-1])
        return a[n - 1] / Integer(n)


class N(FormalPowerSeries):
    def __init__(self, a, *args, **kwargs):
        """
        Description and tests at FormalPowerSeries.n
        sage: None # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, FormalPowerSeriesRing(num(0, *args, **kwargs).parent()), min_index=a.min_index)

        self.a = a
        self.args = args
        self.kwargs = kwargs

    def coeffs(self, k):
        """ sage: None # indirect doctest """
        return num(self.a[k], *self.args, **self.kwargs)


class Regit_hyp(FormalPowerSeries0):
    def __init__(self, a, t, is_pow=False):
        """
        Description and tests at FormalPowerSeries.regit
        sage: None   # indirect doctest
        """
        A = a.parent()
        AB = A.base_ring()
        T = t.parent()
        if is_pow is False:
            base_ring = (a[1]**t).parent()
        else:
            if T.has_coerce_map_from(AB):
                base_ring = T
            elif AB.has_coerce_map_from(T):
                base_ring = AB

        # if is_pow is False and AB.has_coerce_map_from(T):
        #     res_type = A
        #     base_ring = None  # will be taken from res_type
        # elif is_pow is False and T.has_coerce_map_from(AB):
        #     res_type = None  # will be computed from base_ring
        #     base_ring = T
        # elif is_pow is True:
        #     base_ring = None  # will be taken from res_type

        si = FormalPowerSeries.__init__
        si(self, FormalPowerSeriesRing(base_ring), min_index=1, base_ring=base_ring)
        self.a = a
        self.t = t
        self.is_pow = is_pow

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        b = self
        a = b.a
        t = b.t
        if a.parent().is_decidable:
            assert a[1] != 1, a[1]
            assert a[1] != 0, a[1]

        # print "(" + repr(n)
        if n == 0:
            # print ")"
            return self.K0
        if n == 1:
            # print ")"
            if self.is_pow:
                return t
            return a[1] ** t

        D = 0
        N = n + D

        res = b.K0
        for d in range(D + 1):
            res -= b[1 + d] * a.npow(1 + d)[N] - a[N - d] * (b.npow(N - d)[N])

        for m in range(2 + D, n):
            res -= b[m] * a.npow(m)[N] - a[m] * b.npow(m)[N]

        res /= a.npow(n)[N] - a[1 + D]
        # print ")"
        return res


class Inv(FormalPowerSeries0):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.inv
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=1)
        self.a = a

    def coeffs(self, n):
        """ sage: None # indirect doctest """
        b = self
        a = self.a
        if n == 0:
            return self.K0
        if n == 1:
            return 1 / a[1]
        if n > 1:
            return - sum([b[k] * a.npow(k)[n] for k in range(1, n)], self.K0) / a[1] ** n


class Logit_hyp(FormalPowerSeries0):
    def __init__(self, a, j1=None):
        """
        Description and tests at FormalPowerSeries.julia_gen
        sage: None   # indirect doctest
        """
        self.a = a

        self.ap = a.diff()

        min_index = a.valit() + 1

        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=min_index)

        if j1 is None:
            self.j1 = log(a[1])
        else:
            self.j1 = j1

    def coeffs(self, n):
        """ sage: None #indirect doctest """

        a = self.a
        ap = self.ap

        r = self.K0

        # joh  = h'*j
        if n < 1:
            return self.K0
        if n == 1:
            return self.j1
        # sum(k=1..n) j_k a^k_n = sum(k=1..n) ap_(n-k) * j_k, ap_0 = a_1 != 0
        # j_n * a_1^n + sum(k=1..n-1) j_k a^k_n = ap_0 * j_n + sum(k=1..n-1) ap_(n-k) * j_k
        for k in range(1, n):
            r += self[k] * (ap[n - k] - a.npow(k)[n])
        return r / (a[1] ** n - a[1])


class Regit01(FormalPowerSeries01):
    def __init__(self, f, t, k=0, a1=None, avp1=None, a0tovp1=None):
        """
        Description and tests at FormalPowerSeries.regit
        sage: None  # indirect doctest
        """
        self.f = f
        self.v = f.valit()
        self.t = t

        si = FormalPowerSeries.__init__
        si(self, f.parent(), min_index=1)

        self.a0tovp1 = a0tovp1

        if a1 is not None:
            self.a1 = a1
        elif k != 0:
            self.a1 = ((QQbar(-1)) ** (1 / self.v)) ** (2 * k)
        else:
            self.a1 = self.K1

        self.avp1 = avp1

    def coeffs(self,n):
        # aoj = joa
        # sum(k=1..N) a_k j^k_N = sum(k=1..N) j_k a^k_N
        # sum(k=1..n) a_k j^k_N + a_N * j_1^N = j_1*h_N + j_{v+1} a^(v+1)_N +...+ j_N a^N_N
        # sum(k=1..n) a_k j^k_N = j_{v+1} a^(v+1)_N +...+ j_N a^N_N
        # a^(v+k+1)_{n+v} on the left does not contain a_n for k > 0
        # a^(v+1)_{n+v}  = a_n*a^v_v +         a_{n-1}*a^v_{v+1}    +...+ a_{v+1}*a^v_{n-1}     + a_1*a^v_{n+v-1}
        # a^v_{n+v-1}    = a_n*a^(v-1)_{v-1} + a_{n-1}*a^{v-1}_v    +...+ a_{v+1}*a^(v-1)_{n-2} + a_1*a^(v-1)_{n+v-2}
        # a^(v-1)_{n+v-2}= a_n*a^(v-2)_{v-2} + a_{n-1}*a^(v-2)_{v-1}+...+ a_{v+1}*a^(v-2)_{n-3} + a_1*a^(v-2)_{n+v-3}
        # ...
        # a^1_n          = a_n

        a = self
        j = self.f
        v = self.v
        t = self.t
        N = n+v

        if self.a0tovp1 is not None and n <= v+1:
            return self.a0tovp1[n]

        if n == 0:
            return self.K0
        if n == 1:
            return self.a1
#        if n <= v:
#            return self.K0
        if n == v+1:
            if self.avp1 is not None:
                return self.avp1
            if self.a1 == self.K1:
                return t*j[n]
            x = var('x')
            vp1 = self.parent([self[k] for k in range(v+1)] + [x] ).nit(v)[v+1]
            return t*v*solve( vp1 == j[v+1], x)[0].right_hand_side()

        rhs = self.K0
        # right side except f_{v+1}*(v+1)*a_n
        for k in range(v + 2, N + 1):
            rhs += j[k] * a.npow(k)[N]
        s = 0
        for k in range(2, n):
            s += a[k] * sum([a[1]**(v-i)*a.npow(i)[n + i - k] for i in range(1, v + 1)], a.K0)
        rhs += j[v + 1] * s
        # left side except a_n * f^n_N = a_n * n * f_(v+1)
        lhs = self.K0
        for k in range(1,n):
            lhs += a[k]*j.npow(k)[N]
        res = (rhs-lhs)/j[v+1]/(n - v - 1)
        #print(N,v,n,lhs,rhs,j[v+1]*n,j[v+1]*sum([a[1]**k for k in range(0,v+1)],a.K0),res)
        return res


class Logit01(FormalPowerSeries01):
    def __init__(self, a, j1=None):
        """
        Description and tests at FormalPowerSeries.julia_gen
        sage: None   # indirect doctest
        """
        self.a = a

        self.ap = a.diff()

        self.v = a.valit()

        if j1 is None or j1 == a.K0:
            min_index = self.v + 1
            self.j1 = a.K0  # log(a[1])
        else:
            min_index = 1
            self.j1 = j1

        si = FormalPowerSeries0.__init__
        si(self, a.parent(), min_index=min_index)

    def coeffs(self, n):
        """ sage: None #indirect doctest """

        a = self.a
        ap = self.ap

        # joh  = h'*j
        if n == 0:
            return self.K0
        if n == 1:
            return self.j1
        if n <= self.v:
            return self.K0
        if n == self.v + 1:
            return a[self.v+1]

        valit = self.v
        N = n + valit

        # sum(k=1..N) j_k a^k_N = sum(k=0..N) ap_(N-k) * j_k, ap_0 = a_1 = 1
        # a^k_N = 0 for n<=k<N; ap_m = 0 for 0 < m < valit
        # j_N * a_1^N + sum(k=1..n) j_k a^k_N = ap_0*j_N + sum(k=0..n) ap_(N-k) * j_k
        # so in case a_1 = 1 = ap_0, we have the recursion
        # j_n * a^n_N + sum(k=1..(n-1)) j_k a^k_N = ap_valit * j_n + sum(k=1..N-1) ap_(N-k) * j_k
        # a^n_N = a_{valit+1} * n

        r = self.K0
        for k in range(1, n):
            r += self[k] * (ap[N - k] - a.npow(k)[N])

        assert ap[valit] == (valit + 1) * a[valit + 1]
        assert a.npow(n)[N] == a[valit + 1] * n, str(a.npow(n)[N]) + "!=" + str(a[N - n + 1] * n) + " n=" + str(
            n) + " N=" + str(N) + str(a)
        assert a.npow(n)[N] - ap[N - n] == a[valit + 1] * (n - valit - 1)
        return r / (a[valit + 1] * (n - (valit + 1)))
        # return r/(a.npow(n)[N]-ap[valit])


class Expit01(FormalPowerSeries01):
    def __init__(self, j, a1=None, **kwargs):
        """
        Description and tests at FormalPowerSeries.julia_gen
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, j.parent(), min_index=1)
        self.j = j
        if a1 is not None:
            self.a1 = a1
        else:
            self.a1 = self.K1

    def coeffs(a, n):
        """ sage: None #indirect doctest """
        j = a.j
        v = j.min_index - 1
        N = n + v
        if n == 0:
            return a.K0
        if n == 1:
            return a.a1
        if n < v + 1:
            return a.K0
        if n == v + 1:
            return j[n]

        # joa  = a'*j
        # sum(k=1..N) j_k a^k_N = sum(k=0..N) (k+1)a_{k+1} * j_{N-k}
        # j_1*a_N + j_{v+1} a^(v+1)_N +...+ j_N a^N_N = a_1*j_N + (v+1)a_{v+1}*j_n +...+ n*a_n * j_{v+1} + N*a_N*j_1
        # a^(v+k+1)_{n+v} on the left does not contain a_n for k > 0
        # a^(v+1)_{n+v}  = a_n*a^v_v +         a_{n-1}*a^v_{v+1}    +...+ a_{v+1}*a^v_{n-1}     + a_1*a^v_{n+v-1}
        # a^v_{n+v-1}    = a_n*a^(v-1)_{v-1} + a_{n-1}*a^{v-1}_v    +...+ a_{v+1}*a^(v-1)_{n-2} + a_1*a^(v-1)_{n+v-2}
        # a^(v-1)_{n+v-2}= a_n*a^(v-2)_{v-2} + a_{n-1}*a^(v-2)_{v-1}+...+ a_{v+1}*a^(v-2)_{n-3} + a_1*a^(v-2)_{n+v_3}
        # ...
        # a^1_n          = a_n

        r = a.K0
        if not j[1] == j.K0:
            ls = sum([j[k]*a.npow(k)[n] for k in range(2,n) if j[k] != a.K0],a.K0)
            rs = sum([(k+1)*a[k+1]*j[n-k] for k in range(0,n-1)],a.K0)
            return (ls - rs)/((N-1)*j[1])

        for k in range(v + 2, N + 1):
            r += j[k] * a.npow(k)[N]
        r -= a[1] * j[N]
        for k in range(v + 1, n):
            r -= k * a[k] * j[N + 1 - k]
        s = 0
        for k in range(v + 1, n):
            s += a[k] * sum([a.npow(i)[n + i - k] for i in range(1, v + 1)])
        r += j[v + 1] * s

        return r / j[v + 1] / (n - v - 1)


class Super(FormalPowerSeries01):
    def __init__(self, f, a0):
        """
        Description and tests at FormalPowerSeries01.super
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, f.parent(), min_index=0)
        self.j = f.logit()
        self.a0 = a0

    def coeffs(a, n):
        """ sage: None #indirect doctest """

        j = a.j

        if n == 0:
            return a.a0
        # print([(k,n-1) for k in range(n)])
        # return 1
        return sum([j[k]*(a.npow(k))[n-1] for k in range(n)], a.K0)/n



class Schroeder(FormalPowerSeries0):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.schroeder
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=1)
        self.a = a
        self.hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        if a.parent().is_decidable:
            assert a[1] != 0, a[1]
            assert a[1] != 1, a[1]

        q = a[1]

        if n <= 0:
            return self.K0
        if n == 1:
            return self.K1
        return sum([self[m] * a.npow(m)[n] for m in range(1, n)], self.K0) / (q - q ** n)


class InvSchroeder(FormalPowerSeries0):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.inv_schroeder
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=1)
        self.a = a

    def coeffs(self, n):
        """sage: None #indirect doctest"""
        a = self.a
        q = a[1]

        if n <= 0:
            return self.K0
        if n == 1:
            return 1
        return sum([a[m] * self.npow(m)[n] for m in range(2, n + 1)], self.K0) / (q ** n - q)


class Regit_Jabotinsky(FormalPowerSeries01):
    def __init__(self, a, t):
        """
        Description and tests at FormalPowerSeries01.regit
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        ps_type = None
        base_ring = None
        if a.base_ring().has_coerce_map_from(t.parent()):
            ps_type = a.parent()
        elif t.parent().has_coerce_map_from(a.base_ring()):
            base_ring = t.parent()
        si(self, ps_type, min_index=a.min_index, base_ring=base_ring)
        self.a = a
        self.t = t
        self.hint = HintType([0, 1])

    def coeffs(self, n):
        """ sage: None   # indirect doctest """
        a = self.a
        t = self.t
        if a.parent().is_decidable:
            assert a[0] == 0, "The index of the lowest non-zero coefficient must be 1, but is " + repr(a.min_index)
            assert a[1] == 1, "The first coefficient must be 1, but is " + repr(a[1])

        if n == 1:
            return self.K1
        # def c(m):
        #    return (-1)**(n-1-m)*binomial(t,m)*binomial(t-1-m,n-1-m)
        # res = sum([c(m)*a.nit(m)[n] for m in range(n)],self.K0)
        # return res

        r = self.K0
        for m in range(n):
            s = self.K0
            for k in range(m + 1):
                s += binomial(m, k) * (-1) ** (m - k) * a.nit(k)[n]
            r += s * binomial(t, m)
        return r


class Logit_Jabotinsky(FormalPowerSeries01):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries01.julia
        sage: None   # indirect doctest
        """
        si = FormalPowerSeries.__init__
        si(self, a.parent(), min_index=1)
        self.a = a

    def coeffs(self, n):
        """ sage: None # indirect doctest """
        a = self.a
        r = self.K0
        P = self.parent()

        for m in range(n):
            s = self.K0
            for k in range(m + 1):
                s += binomial(m, k) * (-1) ** (m - k) * a.nit(k)[n]
            s *= P.Stirling1[m][1] / factorial(m)
            r += s

        return r


class Crush(FormalPowerSeries):
    def __init__(self, a):
        """
        Description and tests at FormalPowerSeries.crush
        sage: None   # indirect doctest
        """

        si = FormalPowerSeries.__init__
        si(self, a.parent().base_ring(), min_index=a.min_index)
        self.a = a
        if hasattr(a, 'hint'):
            self.hint = a.hint

    def coeffs(self, n):
        return sum([self.a[k][n - k] for k in range(self.min_index, n + 1)], self.K0)

