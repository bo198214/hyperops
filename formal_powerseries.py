"""
Cached formal powerseries and formal Laurant series in one variable.

Author: Henryk Trappmann
"""

from sage.structure.sage_object import SageObject
from sage.rings.arith import factorial
from sage.rings.arith import binomial
from sage.rings.integer import Integer
from sage.calculus.calculus import SymbolicExpression, SymbolicVariable, var, log
from sage.calculus.functional import diff
from sage.rings.ring import Ring
from sage.rings.ring_element import RingElement
from sage.rings.rational_field import QQ, RationalField
from sage.rings.rational import Rational
from sage.rings.real_mpfr import RR, RealField
from sage.rings.complex_field import ComplexField_class
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_ring import PolynomialRing_field
from sage.misc.misc_c import prod
from sage.rings.infinity import Infinity
from sage.rings.power_series_ring_element import PowerSeries
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.matrix.constructor import matrix

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
    if isinstance(K,RationalField):
        return True
    if isinstance(K,PolynomialRing_field):
        return True
    #            if isinstance(K,RealField):
    #                return true
    #            if isinstance(K,ComplexField_class):
    #                return true
    return False

class FormalPowerSeriesRing(Ring):
    def by_lambda(self,f,*args,**kwargs):
        """
        Returns the powerseries with coefficients f(n).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.by_lambda(lambda n: 1/factorial(n))
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]

        Initialization as formal Laurant series:
        sage: P.by_lambda(lambda n: n,-3)               
        [-3, -2, -1; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, ...]

        Corruptly setting min_index=3
        sage: P.by_lambda(lambda n: n,3)
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, ...]

        Properly setting min_index=3
        sage: P.by_lambda(lambda n: n,3,complies=False)
        [0, 0, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, ...]
        """
        kwargs['parent'] = self
        if kwargs.has_key('T'):
            T = kwargs['T'] 
            del kwargs['T']
            return T(f,*args,**kwargs)
        else:
            return FormalPowerSeries(f,*args,**kwargs)


    def by_iterator(self,g,min_index=0):
        """
        Returns a powerseries from the generator g.
        The powerseries coefficients start at min_index
        which is allowed be negative obtaining a formal Laurant series.

        
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.by_iterator(iter(ZZ),-2) 
        [0, 1; -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 7, -7, 8, -8, 9, -9, 10, -10, ...]
        """
        res = self.by_undefined()
        res.min_index = min_index
        def f(n):
            """ sage: None # indirect doctest """
            if n<min_index:
                return 0
            if n==min_index:
                return g.next()
            x = res[n-1] #dummy to compute the prev value
            return g.next()
        res.f = f
        return res
        
    def by_undefined(self,T=None):
        """
        Returns an undefined powerseries. This is useful to use method `define'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P.by_undefined()         
        sage: a
        Undefined
        """
        if T==None:
            return FormalPowerSeries()
        return T()
    
    def by_sequence(self,list,start=0,**kwargs):
        """
        Returns the powerseries with coefficients p[n] where
        p[n]==0 for 0<=n<start, p[m+start]==list[m] for all list indices m,
        and p[n]==0 for all later indices n.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)                         
        sage: f = P.by_sequence([1,2,3,4,5])
        sage: f
        [1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.by_sequence([1,2,3],5)
        [0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        l = len(list)
        M=0
        for M in range(l):
            if list[M] != 0:
                break
        N=-1
        for i in range(l):
            N = l-i-1
            if list[N] != 0:
                break

        min_index = start + M
        max_index = start + N
        def f(k):
            """ sage: None   # indirect doctest """
            if k<min_index or k>max_index:
                return 0
            return list[k-start]

        return self.by_lambda(f,min_index,**kwargs)

    def by_polynomial(self,p):
        """
        Returns the FormalPowerSeries from the given Polynomial.
        """
        return self.by_sequence(p.padded_list())

    def by_powerseries(self,p):
        """
        Returns the FormalPowerSeries from the given PowerSeries.
        """
        return self.by_polynomial(p.polynomial())
        
    def by_taylor(self,expr,v,at=0,**kwargs):
        """
        Returns the taylor series of `expr' with respect to `v' at `at'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ) 
        sage: f = P.by_taylor(ln(x),x,1)   
        sage: f
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        """
        assert not v == None
        assert isinstance(v,SymbolicVariable)

        def f(n):
            """ sage: None   # indirect doctest """
            #too slow
            #if not at == 0 and n==0:
            #    return expr({v:at})-at
            #return simplify(diff(expr,v,n).substitute({v:at})/factorial(n))
            return self.K(expr.taylor(v,at,n).substitute({v:v+at}).coeff(v,n))

        #coeffs always returns non-empty list, at least [0,0] is contained
        min_index = expr.taylor(v,at,2).substitute({v:v+at}).coeffs(v)[0][1]
        #print "after",min_index
        return self.by_lambda(f,min_index,**kwargs)

    def by_constant(self,c,**kwargs):
        """
        Returns the powerseries with coefficients [c,0,0,...].

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: f = P.by_constant(42)
        sage: f
        [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        def f(n):
            """ sage: None   # indirect doctest """
            if n == 0:
                return self.K(c)
            return 0
        return self.by_lambda(f,0,**kwargs)
        

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

    def zero_element(self):
        """
        Returns the zero element of this power series ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.zero_element()             
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return self.Zero

    def one_element(self):
        """
        Returns the one element of this power series ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.one_element()              
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return self.One
        
    def __call__(self,p=None,v=None,at=None,**kwargs):
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

        See also methods: by_const, by_undef, by_sequence, by_taylor, by_lambda
        """

        if isinstance(p,Integer) or isinstance(p,int) or isinstance(p,Rational):
            return self.by_constant(p,**kwargs)

        if isinstance(p,list):
            return self.by_sequence(p,**kwargs)

        if isinstance(p,SymbolicExpression):
            if at == None:
                at = 0
            return self.by_taylor(p,v,at,**kwargs)

        if isinstance(p,Polynomial):
            return self.by_polynomial(p)

        if isinstance(p,PowerSeries):
            return self.by_powerseries(p)

        #TODO generator if isinstance(p,

        if type(p) is type(lambda n: 0):
            if at == None:
                at = 0
            return self.by_lambda(p,at,**kwargs)

        return self.by_undefined()

    def __init__(self,base_ring):
        """
        Returns the powerseries ring over base_ring.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ) 
        FormalPowerSeriesRing over Rational Field
        """
        if base_ring == None:
            return

        self.K = base_ring

        def PSF(f):
            """ sage: None   # indirect doctest """
            return self.by_lambda(f,T=FormalPowerSeries)
        def PSF01(f):
            """ sage: None   # indirect doctest """
            return self.by_lambda(f,T=FPS01)
        def PSS(seq):
            """ sage: None   # indirect doctest """
            return self.by_sequence(seq,T=FormalPowerSeries)

        if self.K == int:
            self.K = Integer

        K = self.K
        K1 = K.one_element()
        self.K1 = K1
        #K0 = K.zero_element()
        K0 = 0
        self.K0 = K0

        self.Zero = PSS([])
        self.Zero.__doc__ = """ 
        The zero element power series.
        """
        self.One = PSS([K1])
        self.One.__doc__ = """
        The one element power series.
        """
        self.Id = self.by_sequence([K1],start=1)
        self.Id.__doc__ = """
        The powerseries of the identity function id(x)=x.
        """
        self.Inc = PSS([K1,K1])
        self.Inc.__doc__ = """
        The powerseries of the increment function inc(x)=x+1.
        """
        self.Dec = PSS([K(-1),K1])
        self.Dec.__doc__ = """
        The powerseries of the decrement function dec(x)=x-1.
        """
        self.Exp = PSF(lambda n: K(1/factorial(n)))
        self.Exp.__doc__ = """
        The powerseries of the exponential function.
        """
        self.Dec_exp = PSF01(lambda n: K0 if n==0 else K(1/factorial(n)))
        self.Dec_exp._doc__ = """
        The powerseries of the decremented exponential dec_exp(x)=exp(x)-1.
        """
        self.Log_inc = PSF01(lambda n: K0 if n==0 else K((-1)**(n+1)/Integer(n)))
        self.Log_inc.__doc__ = """
        The powerseries of the logarithm at 1 
        or the powerseries of f(x)=log(x+1) at 0.
        """
        self.Sin = PSF01(lambda n: K0 if n % 2 == 0 else K((-1)**((n-1)/2)/factorial(n)))
        self.Sin.__doc__ = """
        The powerseries of the sine.
        """
        self.Cos = PSF(lambda n: K0 if n % 2 == 1 else K((-1)**(n/2)/factorial(n)))
        self.Cos.__doc__ = """
        The powerseries of the cosine.
        """

        def arcsin(n):
            """ sage: None   # indirect doctest """
            if n % 2 == 0:
                return K0
            evenprod = Integer(1)
            oddprod = Integer(1)
            for k in range(2,n):
                if k % 2 == 0:
                    evenprod *= k
                else:
                    oddprod *=k
            return K(oddprod/evenprod/n)
                            
        self.Arcsin = PSF01(arcsin)
        self.Arcsin.__doc__ = """
        The powerseries of arcsin.
        """
        self.Arctan = PSF01(lambda n: K0 if n % 2== 0 else K((-1)**(n/2)/Integer(n)))
        self.Arctan.__doc__ = """
        The powerseries of arctan.
        """
        self.Sinh = PSF01(lambda n: K0 if n % 2 == 0 else K(1/factorial(n)))
        self.Sinh.__doc__ = """
        The powerseries of sinh.
        """
        self.Cosh = PSF(lambda n: K0 if n % 2 == 1 else K(1/factorial(n)))
        self.Cosh.__doc__ = """
        The powerseries of cosh.
        """
        def arcsinh(n):
            """ sage: None   # indirect doctest """
            if n % 2 == 0:
                return K0
            evenprod = Integer(1)
            oddprod = Integer(1)
            for k in range(2,n):
                if k % 2 == 0:
                    evenprod *= k
                else:
                    oddprod *= k
            return K((-1)**(n/2)*oddprod/evenprod/n)
        self.Arcsinh = PSF01(arcsinh)
        self.Arcsinh.__doc__ = """
        The powerseries of arcsinh.
        """
        self.Arctanh = PSF01(lambda n: K0 if n % 2 == 0 else K(1/Integer(n)))
        self.Arctanh.__doc__ = """
        The powerseries of arctanh.
        """

        self.Bernoulli = (self.Id / self.Exp.dec()).derivatives()
        self.Bernoulli.__doc__ = """
        The n-th Bernoulli number is equal to 
        the n-th derivative of 1/(exp(x)-1) at 0.
        """

        def tan(N):
            """ sage: None   # indirect doctest """
            if N % 2 == 0:
                return K0
            n = (N + 1) / 2
            return K(self.Bernoulli[2*n] * (-4)**n * (1-4**n) / factorial(2*n))
        self.Tan = PSF01(tan)
        self.Tan.__doc__ = """
        The powerseries of tan.
        """

        def tanh(N):
            """ sage: None   # indirect doctest """
            if N % 2 == 0:
                return K0
            n = (N+1)/2
            return K(self.Bernoulli[2*n] * (-1)**(2*n) * 4**n * (4**n-1) / factorial(2*n))
        self.Tanh = PSF01(tanh)
        self.Tanh.__doc__ = """
        The powerseries of tanh.
        """

        self.Xexp = PSF01(lambda n: K0 if n==0 else K(1/factorial(n-1)))
        self.Xexp.__doc__ = """
        The powerseries of x*exp(x)
        """

        self.Lambert_w = PSF01(lambda n: K0 if n==0 else K((-n)**(n-1)/factorial(n)))
        self.Lambert_w.__doc__ = """
        The Lambert W function is the inverse of f(x)=x*e^x 
        """

        def sqrt_inc(n):
            """ sage: None   # indirect doctest """
            evenprod=Integer(1)
            oddprod=Integer(1)
            for k in range(2,2*n+1):
                if k%2 == 0:
                    evenprod *= k
                else:
                    oddprod *= k
            return K((-1)**n *oddprod/evenprod/(1-2*n))
        self.Sqrt_inc = PSF(sqrt_inc)
        self.Sqrt_inc.__doc__ = """
        The powerseries of sqrt at 1, or of sqrt(x+1) at 0.
        """

        #dont go into a recursion defining stirling1
        if isinstance(K,FormalPowerSeriesRing):
            return

        self.Stirling1 = FormalPowerSeries(parent=self)
        def f(n):
            """ sage: None   # indirect doctest """
            
            if n==0:
                res = self.by_lambda(lambda k: 1 if k==0 else 0)
            else:
                g = self.Stirling1[n-1]
                res = self.by_lambda(lambda k: g[k-1]-(n-1)*g[k],1)
        
            return res
        self.Stirling1.f = f
        self.Stirling1.__doc__ = """
        Returns the sequence of Stirling numbers of the first kind.
        These are the coefficients of the polynomial x(x-1)(x-2)...(x-n+1).
        stirling1[n][k] is the coefficient of x^k in the above polynomial.
        """

        def lehmer_comtet(n,k): #A008296
            """ sage: None   # indirect doctest """
            return sum([binomial(l, k)*k^(l-k)*self.Stirling1[n][l] for l in range(k,n+1)],K0)
        self.Lehmer_comtet = PSF(lambda n: sum([k**(n-k)*binomial(n,k) for k in range(n+1)],K0))
        self.A000248  = self.Lehmer_comtet
        self.Lehmer_comtet.__doc__ = """
        The n-th Lehmer-Comtet number is the n-th derivative of x^x at 1.
        See Sloane A008296.
        """

        #self.selfpower_inc = PSF(lambda n: K(sum([ lehmer_comtet(n,k) for k in range(0,n+1))/factorial(n),K0))
        self.Selfpower_inc = PSF(lambda n: K(sum([ self.Stirling1[n][k]*self.A000248[k] for k in range(n+1)],K0)/factorial(n)))
        self.Selfpower_inc.__doc__ = """
        The powerseries of x^x at 1.
        """
        self.Superroot_inc = PSF(lambda n: K(sum([ self.Stirling1[n][k]*Integer(1-k)**(k-1) for k in range(n+1)],K0)/factorial(n)))
        self.Superroot_inc.__doc__ = """
        The powerseries of the inverse of x^x developed at 1.
        """

        def A003725(n):
            """ sage: None   # indirect doctest """
            return K(sum([ (-k)**(n-k)*binomial(n, k) for k in range(n+1)],K0))
        self.A003725 = PSF(A003725)
        self.A003725.__doc__ = """
        The derivatives of exp(x*e^(-x)) at 0.
        """

        self.Selfroot_inc = PSF(lambda n: K(sum([ self.Stirling1[n][k]*self.A003725[k] for k in range(n+1)],K0)/factorial(n)))
        self.Selfroot_inc.__doc__ = """
        The powerseries of x^(1/x) at 1.
        """

        self.Inv_selfroot_inc = PSF(lambda n: K(sum([self.Stirling1[n][k]*K((k+1))**(k-1) for k in range(n+1)],K0)/factorial(n)))
        self.Inv_selfroot_inc.__doc__ = """
        The inverse of the self root x^(1/x) at 1.
        The inverse of the self root for x=b is the fixed point of f(y)=b^y.
        """

    def _repr_(self):
        """
        Description of this FormalPowerSeriesRing.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ)._repr_()            
        'FormalPowerSeriesRing over Rational Field'
        """
        return "FormalPowerSeriesRing over " + repr(self.K)

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
        sage: from sage.rings.formal_powerseries import *
        sage: P = FormalPowerSeriesRing(QQ)
        
        sage: P.Exp
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        sage: P.Log_inc
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        sage: P.Sin
        [0, 1, 0, -1/6, 0, 1/120, 0, -1/5040, 0, 1/362880, 0, -1/39916800, 0, ...]
        sage: P.Cos
        [1, 0, -1/2, 0, 1/24, 0, -1/720, 0, 1/40320, 0, -1/3628800, 0, 1/479001600, ...]
        sage: P.Arcsin
        [0, 1, 0, 1/6, 0, 3/40, 0, 5/112, 0, 35/1152, 0, 63/2816, 0, 231/13312, 0, ...]
        sage: P.Arctan
        [0, 1, 0, -1/3, 0, 1/5, 0, -1/7, 0, 1/9, 0, -1/11, 0, 1/13, 0, -1/15, 0, ...]
        sage: P.Sinh
        [0, 1, 0, 1/6, 0, 1/120, 0, 1/5040, 0, 1/362880, 0, 1/39916800, 0, ...]
        sage: P.Cosh
        [1, 0, 1/2, 0, 1/24, 0, 1/720, 0, 1/40320, 0, 1/3628800, 0, 1/479001600, 0, ...]
        sage: P.Arcsinh
        [0, 1, 0, -1/6, 0, 3/40, 0, -5/112, 0, 35/1152, 0, -63/2816, 0, 231/13312, ...]
        sage: P.Arctanh
        [0, 1, 0, 1/3, 0, 1/5, 0, 1/7, 0, 1/9, 0, 1/11, 0, 1/13, 0, 1/15, 0, 1/17, ...]
        sage: P.Bernoulli
        [1, -1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, ...]
        sage: P.Tan
        [0, 1, 0, 1/3, 0, 2/15, 0, 17/315, 0, 62/2835, 0, 1382/155925, 0, ...]
        sage: P.Tanh
        [0, 1, 0, -1/3, 0, 2/15, 0, -17/315, 0, 62/2835, 0, -1382/155925, 0, ...]
        sage: P.Sqrt_inc
        [1, 1/2, -1/8, 1/16, -5/128, 7/256, -21/1024, 33/2048, -429/32768, ...]
        sage: P.Lambert_w
        [0, 1, -1, 3/2, -8/3, 125/24, -54/5, 16807/720, -16384/315, 531441/4480, ...]
        sage: P.Selfpower_inc
        [1, 1, 1, 1/2, 1/3, 1/12, 3/40, -1/120, 59/2520, -71/5040, 131/10080, ...]
        sage: P.Superroot_inc
        [1, 1, -1, 3/2, -17/6, 37/6, -1759/120, 13279/360, -97283/1008, ...]
        sage: P.A003725
        [1, 1, -1, -2, 9, -4, -95, 414, 49, -10088, 55521, -13870, -2024759, ...]
        sage: P.Selfroot_inc
        [1, 1, -1, 1/2, 1/6, -3/4, 131/120, -9/8, 1087/1260, -271/720, -2291/10080, ...]
        sage: P.Inv_selfroot_inc
        [1, 1, 1, 3/2, 7/3, 4, 283/40, 4681/360, 123101/5040, 118001/2520, ...]


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

        sage: P.Exp.dec() | P.Log_inc 
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Sin | P.Arcsin 
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Tan | P.Arctan
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Tanh | P.Arctanh
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Xexp | P.Lambert_w
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Superroot_inc.dec() | P.Selfpower_inc
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Inv_selfroot_inc.dec() | P.Selfroot_inc
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


        sage: P([0,1,0,2]).abel_coeffs()
        [3/2, [-1/4, 0; 0, 0, -5/4, 0, 21/8, 0, -35/4, 0, 2717/80, 0, -13429/100, 0, ...]]
        sage: p = P([0,1,0,0,1,2,3])
        sage: a = p.abel_coeffs()
        sage: a
        [6, [-1/3, 1, -1; 0, -10, 11/2, 17/9, -169/12, 349/30, 13/18, -544/21, 1727/24, ...]]
        sage: ((p << 1).log().scalm(a[0]) + (p | a[1]) - a[1]).reclass()
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: a = var('a')
        sage: p = FormalPowerSeriesRing(PolynomialRing(QQ,a))(exp(a*x)-1,x,T=FPS0)
        sage: pah = p.abel()
        sage: pac = p.abel2()
        sage: pah
        [0, 1/2*a/(-a + 1), (5/24*a^3 + 1/24*a^2)/(a^3 - a^2 - a + 1), ...]
        sage: pac
        [0, -1/2*a/(a - 1), (5/12*a^3 + 1/12*a^2)/(2*a^3 - 2*a^2 - 2*a + 2), ...]
        sage: [pac[k] - pah[k]==0 for k in range(0,5)]
        [True, True, True, True, True]
        sage: P._test()
        """
        pass

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

        sage: #power series operations                                                        
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
        sage: dexp = (expps - one)
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
        sage: dexp.it(x)[5].expand()
        x^4/16 - 13*x^3/144 + x^2/24 - x/180
        sage: q = dexp.it(1/x).it(x)

        sage: expand(q[3])
        1/6
        sage: dexp[3]
        1/6

        sage: #you can initialize power series with arbitrary functions on natural numbers    
        sage: #for example the power series of sqrt(2)^x can be given as                      
        sage: bsrt = FormalPowerSeriesRing(SR)(sqrt(2)^x,x)

        sage: #making the 0-th coefficient 0 to get the decremented exponential   
        sage: dbsrt = bsrt.ps0()
        
        sage: #and now starting hyperbolic iteration                                          
        sage: dbsrt2 = dbsrt.it(x).it(1/x)
        sage: #Sage is not able to simplify                                                   
        sage: simplify(dbsrt2[3])
        (log(2)^3*(log(2)^(x + 2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)*2^x) - log(2)^3*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(8*(log(2)^2/4 - log(2)/2)) - log(2)^(x + 3)*2^(-x - 4)/3 + log(2)^(3*x + 3)*2^(-3*x - 4)/3)/(8*(log(2)^3/8 - log(2)/2)) - log(2)*(log(2)^(x + 2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)*2^x) - log(2)^3*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(8*(log(2)^2/4 - log(2)/2)) - log(2)^(x + 3)*2^(-x - 4)/3 + log(2)^(3*x + 3)*2^(-3*x - 4)/3)/(2*(log(2)^3/8 - log(2)/2)) - 2*log(2)^x*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))*(log(2)^2*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)) - log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(2*(log(2)^2/4 - log(2)/2)))/((log(2)^2/4 - log(2)/2)*2^x*(log(2)^(2*x)/2^(2*x) - log(2)^x/2^x)) + log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))*(log(2)^2*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)) - log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(2*(log(2)^2/4 - log(2)/2)))/((log(2)^2/4 - log(2)/2)*(log(2)^(2*x)/2^(2*x) - log(2)^x/2^x)))/(log(2)^(3*x)/2^(3*x) - log(2)^x/2^x)
        sage: #but numerically we can verify equality                                         
        sage: RR(dbsrt2[3](x=0.73)-dbsrt[3])
        -8.67361737988404e-19
    """

    def __init__(self,f=None,min_index=0,complies=True,base_ring=None,parent=None):
        """
        Returns the formal powerseries. 
        
        This method should only be called from FormalPowerSeriesRing.
        See the description there how to obtain a FormalPowerSeries.
        """
        self._parent = parent
        if parent == None:
            if base_ring==None:
                self._parent = FormalPowerSeriesRing(QQ)
            else:
                self._parent = FormalPowerSeriesRing(base_ring)

        self.min_index = min_index #the minimal non-zero index
        self._memo = {}
        self._powMemo = {}
        self._itMemo = {}

        self.K = self._parent.K

        self.min_index = min_index
        if complies:
            self.f = f
        else:
            self.f = lambda n: f(n) if n >= min_index else 0

        if not f==None:
            self.reclass()
            
    def FormalPowerSeries(self,f=None,min_index=0,**kwargs):
        """ 
        Returns a FormalPowerSeries from the 
        same parent.
        """
        return FormalPowerSeries(f,min_index,parent=self._parent,**kwargs)

    def parent(self):
        """
        The FormalPowerSeriesRing to which this FormalPowerSeries belongs.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(1).parent() == P
        True
        """
        return self._parent

#    def new(self,f=None,min_index=0,**kwargs):
#        return type(self)(f,parent=self._parent,**kwargs)
        
    def base_ring(self):
        """
        Returns the base ring of the FormalPowerSeriesRing 
        this FormalPowerSeries is contained in.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: FormalPowerSeriesRing(QQ).by_constant(1).base_ring() == QQ
        True
        """
        return self._parent.K

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

    def define(self,p):
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
        """
        self.f = p.f
        
    def __getitem__(self,n):
        """
        Returns the n-th coefficient of this powerseries: self[n].
        This is the coefficient of x^n.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3])[1] == 2
        True
        """

        if not self._memo.has_key(n):
            #self._memo[n] = simplify(expand(self.f(n)))
            self._memo[n] = self.f(n)
        return self._memo[n]

    def __getslice__(self,i,j): # [i:j]
        """
        Returns the list of coefficients with indices in range(i,j).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n)[1:3]
        [1, 2]
        """
        return [self[k] for k in range(i,j)]

    def set_min_index(a,min_index):
        """
        Returns the powerseries with elements before min_index replaced by 0.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n).set_min_index(5)
        [0, 0, 0, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, ...]
        sage: P(lambda n: n).set_min_index(-5)
        [-5, -4, -3, -2, -1; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, ...]
        """
        return a.FormalPowerSeries(a.f,min_index,complies=False)

    def reclass(p):
        """
        Recalculates the class of this object which 
        possibly changes to a subclass having more operations available.
        Returns p.

        """

        if not decidable0(p.K):
            return p

        min_index = 2
        for n in range(p.min_index,2):
            if not p[n] == 0:
                min_index = n
                break

        p.min_index = min_index

        if p.min_index < 0:
            return p

        if p[0] == 0:
            if p[1] == 1:
                p.__class__ = FPS01
                return p
            p.__class__ = FPS0
            return p
        return p
            
    def ps0(a):
        """
        Returns a, with a[0]=0
        """
        return FPS0(lambda n: 0 if n == 0 else a[n], parent=a._parent)

    def FPS0(self,f=None,**kwargs):
        """
        Returns a FPS0 from the same parent.
        
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([1,2,3])          
        sage: q = p.FPS0(lambda n: -n)
        sage: p.parent() == q.parent()
        True
        """
        return FPS0(f,parent=self._parent,**kwargs)

    def set_element(a, index, value):
        """
        Returns the powerseries that has a[index] replaced by value.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).set_element(1,42)
        [1, 42, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.FormalPowerSeries(lambda n: value if n == index else a[n],a.min_index)

    def set_slice(a, i, j, seq):
        """
        Returns the powerseries that has a[i:j] replaced by seq.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n).set_slice(5,10,[42,43,44,45,46])
        [0, 1, 2, 3, 4, 42, 43, 44, 45, 46, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, ...]
        """
        return a.FormalPowerSeries(lambda n: seq[n-i] if i<=n and n<j else a[n],a.min_index)

    def derivatives(a):
        """
        The sequence of derivatives a[n]*n! of the powerseries a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.derivatives()                                   
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ...]
        """
        return a.FormalPowerSeries(lambda n: a[n]*a.K(factorial(n)))

    def underivatives(a):
        """
        Returns the sequence a[n]/n!.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: 1).underivatives() - P.Exp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.FormalPowerSeries(lambda n: a[n]/a.K(factorial(n)))

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
        return a.FormalPowerSeries(lambda n: a[0]+a.K(1) if n==0 else a[n])

    def dec(a):
        """
        Decrement: a - One.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)

        sage: P.Zero.dec()
        [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.FormalPowerSeries(lambda n: a[0]-a.K(1) if n==0 else a[n])

    def scalm(a,s):
        """
        Scalar multiplication with scalar s
        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).scalm(2)
        [2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.FormalPowerSeries(lambda n: a[n]*s,a.min_index)

    def add(a,b):
        """
        Addition of two powerseries.

        Alternative expression: a.add(b) == a+b

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).add(P([4,5,6]))
        [5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        def f(n):
            """ sage: None   # indirect doctest """
            if n < a.min_index:
                if n < b.min_index:
                    return 0
                return b[n]
            if n < b.min_index:
                return a[n]
            return a[n]+b[n]
        return a.FormalPowerSeries(f,min(a.min_index,b.min_index))

    def __add__(a,b):
        """
        Addition of two powerseries: a+b.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3])+P([4,5,6])
        [5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.add(b)

    def __sub__(a,b): 
        """
        Subtraction of two powerseries: a-b.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n) - P(lambda n: n)
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P([0,1]) - P([1,0])          
        [-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        def f(n):
            """ sage: None   # indirect doctest """
            if n < a.min_index:
                if n < b.min_index:
                    return 0
                #a[0]==0
                return -b[n]
            if n < b.min_index:
                #b[0]==0
                return a[n]
            return a[n]-b[n]
        return a.FormalPowerSeries(f,min(a.min_index,b.min_index))

    def sub(a,b):
        """
        Subtraction of two powerseries.

        Alternative expression: a.sub(b) == a-b

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: n).sub(P(lambda n: n))
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a-b

    def neg(a):
        """
        Negation of the powerseries a.

        Alternative expression a.neg() == -a.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: 1).neg()         
        [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, ...]
        """
        def f(n):
            """ sage: None   # indirect doctest """
            if n < a.min_index:
                return 0
            return -a[n]
        return a.FormalPowerSeries(f,a.min_index)

    def __neg__(a):
        """
        Negation of powerseries: -a.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: -P(lambda n: 1)
        [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, ...]
        """
        return a.neg()

    def mul(a,b): 
        """
        Multiplication of two powerseries.
        This a lazy algorithm: for initial 0 in a[k] and initial 0 in b[n-k] 
        the corresponding b[n-k] or a[k] is not evaluated.

        Alternative expression: a.mul(b) == a*b

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(lambda n: 1).mul(P(lambda n:1))
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, ...]
        """
        #multiplication of two powerseries

        def ab(m,n):
            """
            Lazy product of a[m] and b[n]
            sage: None # indirect doctest
            """
            if a[m] == a.K(0):
                return a.K(0)
            return a[m]*b[n]

        def f(n):
            """ sage: None   # indirect doctest """
            return sum([ab(k,n-k) for k in range(a.min_index,n+1-b.min_index)],a.K(0))

        min_index = a.min_index+b.min_index
        if min_index > 0:
            return a.FPS0(f,min_index=min_index)
        else:
            return a.FormalPowerSeries(f,min_index=min_index)

    def __mul__(a,b):
        """
        Multiplication of two powerseries a*b.
        For documentation see: `mul'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,1])*P([1,1])
        [1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.mul(b)

    def div(c,b):
        """
        Division.
        Alternative expression: c.div(b) == c/b

        Precondition: b != Zero
        It satisfies: a/b*b=a, a*b/b=a

        If c[0]==0 it returns a formal Laurant series, i.e. min_index < 0.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).div(P([2,3,4]))
        [1/2, 1/4, 1/8, -11/16, 25/32, 13/64, -239/128, 613/256, 73/512, ...]
        """
        a = c.FormalPowerSeries()
        b.min_index = b.val()
        a.min_index = c.min_index - b.min_index

        def ab(m,n):
            """
            Lazy product of b[n] and a[m].
            sage: None # indirect doctest
            """
            if b[n] == b.K(0):
                return b.K(0)
            return a[m]*b[n]

        def f(n):
            """ sage: None   # indirect doctest """
            if n<a.min_index:
                return 0
            return (c[n+b.min_index] - sum([ab(k,n+b.min_index-k) for k in range(a.min_index,n)],c.K(0)))/b[b.min_index]
        a.f = f
        return a

    def __div__(c,b):
        """
        Division of two powerseries a/b.
        For documentation see: `div'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.One/P(lambda n: (-1)**n)
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return c.div(b)


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
        return a._parent.One/a

    def npow(a,n):
        """
        Power with natural exponent n.
        This function is cached, it remembers the power for each n.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3]).npow(2)/P([1,2,3])
        [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        if (not isinstance(n,Integer) and not isinstance(n,int)) or n<0:
            raise TypeError, type(n)
        if not a._powMemo.has_key(n):
            if n==0:
                res = a._parent.One
            elif n==1:
                res = a
            else:
                res = a.npow(n-1) * a
            a._powMemo[n] = res
        return a._powMemo[n]

    def nipow(a,t):
        """
        Non-integer power of a (works also for integers but less efficiently). 
        a[0] must be nonzero and a[0]**t must be defined
        as well multiplication of t with all coefficients.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.nipow(1/2)
        [1, 1/2, 1/8, 1/48, 1/384, 1/3840, 1/46080, 1/645120, 1/10321920, ...]

        sage: PR = FormalPowerSeriesRing(RealField(20))
        sage: PR.Exp.nipow(0.5)                       
        [1.0000, 0.50000, 0.12500, 0.020833, 0.0026041, 0.00026041, 0.000021577, ...]
        """
        da = a.set_element(0,0)

        def f(n):
            """ sage: None   # indirect doctest """
            if decidable0(a.K):
                assert a[0] != 0, "0th coefficient is " + repr(a[0]) + ", but must be non-zero for non-integer powers"

            return sum([binomial(t,k) * a[0]**t/a[0]**k * da.npow(k)[n] for k in range(n+1)],a.K(0))
        return a.FormalPowerSeries(f)

    def pow(a,t):
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
        """

        if isinstance(t,FormalPowerSeries):
            P = a._parent
            return ( a.log() * t ) | P.Exp
        if isinstance(t,Integer) or isinstance(t,int):
            if t >= 0:
                return a.npow(t)
            return a.rcp().npow(-t)
        return a.nipow(t)

    def __pow__(a,t): # **
        """
        The t-th (possibly non-integer) power of a.
        For documentation see: `pow'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(RealField(16))
        sage: P([1,2,3])**(-0.37)
        [1.000, -0.7400, -0.09619, 1.440, -2.228, 0.6642, 4.092, -9.079, 6.390, ...]
        """
        return a.pow(t)


    def sqrt(a):
        """
        Square root of a. a.sqrt() * a.sqrt() == a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,1]).sqrt()
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.rt(2)

    def rt(a,n):
        """
        n-th root of a. a.rt(n)**n == a

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        
        sage: P([1,3,3,1]).rt(3)
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.nipow(1/Integer(n))

    def log(a):
        """
        Logarithm of powerseries a with a[0]==1.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.log()           
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        P = a._parent

        dec_a = a.ps0()

#        if decidable0(a.K):
#            assert a[0] == 1
        return dec_a | P.Log_inc
    
#     def __xor__(a,t): # ^
#         #Not recognized as it seems to be mapped to ** in sage
#         return NotImplemented

    def bell(a,k):
        """
        The sequence of Bell polynomials (of the second kind)
        [B_{0,k}(a[1],a[2],...),B_{1,k}(a[1],a[2],...),...]

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: PP = FormalPowerSeriesRing(QQ)

        """
        return (a.underivatives()**k).derivatives().scalm(1/factorial(k))

    def bell_polynomial(a,n,k):
        return a.bell(k)[n]
        

    def genfunc(a,n):
        """
        Returns the generating function of this powerseries up to term
        a[n-1]*x**(n-1).

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: f = P.by_sequence([1,2,3],-2).polynomial(5)                  
        sage: g = P.by_sequence([1,2,3],-2).genfunc(5)
        sage: f(3.7)==g(3.7)
        True
        """
        m = a.min_index
        return lambda x: sum([a[k]*x**k for k in range(m,n)],a.K(0))
        
    def polynomial(a,n,x=var('x')):
        """
        Returns the associated polynomial for the first n coefficients.
        f_0 + f_1*x + f_2*x^2 + ... + f_{n-1}*x^{n-1}

        In case of a Laurant series with e.g. min_index=-2:
        f_{-2} x^(-2) + f_{-1} x^(-1) + ... + f_{n-1}*x^{n-1}
        
        You can adjust the variable by setting x.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.by_sequence([0,1,2]).polynomial(5).padded_list()
        [0, 1, 2]
        """

#        return PolynomialRing(a.K,x)(sum([a[k]*x**k for k in range(n)],a.K(0)))
        P = PolynomialRing(a.K,x)
        m = a.min_index
        if m >= 0:
            return P(a[:n])
        return P(a[m:n])/P(x**(-m))

    def _assertp0(a):
        """
        Asserts a[0]==0.
        """
        assert a.min_index > 0, "min_index must be > 0, but is " + repr(a.min_index) + ". Use reclass() if necessary."

    def _repr_(a):
        """
        Returns a string representation of a, as list of the first
        coefficients.
        If it is a formal Laurant series 
        the coefficients before index 0 are seperated by ";"
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
        if a.f == None:
            return "Undefined"
        res = "["
        if a.min_index < 0:
            for k in range(a.min_index,0):
                res += repr(a[k])
                if k==-1:
                    res += "; "
                else:
                    res += ", "
        for n in range(80):
            coeff = a[n]
            s = repr(a[n]) + ", "
            if len(res)+len(s) > 76: break
            else: res += s

        res += "...]";
        #res = repr([ a(m) for m in range(10)])
        return res

    def complex_contour(a,N,fp=0):
        """
        Returns a contour plot of this powerseries.
        Experimental yet.
        """
        r = abs(a[N])**(-1/Integer(N))
        l = r/sqrt(2.0)
        f = a.polynomial(N)
        x0=real(fp)
        y0=imag(fp)
        return contour_plot(lambda x,y: real(f(CC(x+i*y-fp))),(x0-l,x0+l),(y0-l,y0+l),fill=false) + contour_plot(lambda x,y: imag(f(CC(x+i*y-fp))),(x0-l,x0+l),(y0-l,y0+l),fill=false)       
                    
#     def it(a,t):
#         if decidable0(a.K) and a[0] != 0:
#             raise ValueError, "0th coefficient of b must be 0"
#         if a[1] == 1: return a.it_par(t)
#         else: return a.it_npar(t)

#     def julia(a):
#         if decidable0(a.K):
#             assert a[0] == 0

#             if a[1] == 1:
#                 return a.julia_par()
#             else:
#                 return a.julia_npar()

#         assert decidable0(a.K)

    def __call__(a,b):
        """
        Composition (left after right): a(b).
        For documentation see: `compose'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,2,3])(P([0,1,2]))
        [1, 2, 7, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        b._assertp0()

        def f(n):
            """ sage: None   # indirect doctest """
            res = sum([a[k]*(b.npow(k)[n]) for k in range(n+1)],a.K(0))
            if a.min_index < 0:
                bi = b.rcp()
                res += sum([a[k]*(bi.npow(-k)[n]) for k in range(a.min_index,0)],a.K(0))
            return res
        return (type(a))(f,a.min_index*b.min_index,parent=a._parent)

    def compose(b,a):
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
        """
        return b(a)

    def val(a):
        """
        Returns the first index i such that a[i] != 0
        Does not terminate if a == 0

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,0,42]).val()
        2
        sage: P.by_sequence([1],-42).val()
        -42
        """
        n = a.min_index
        while a[n] == 0:
            n += 1
        return n

    def __lshift__(a,m=1):
        """
        Returns the powerseries with coefficients shiftet to the left by m.
        The coefficients a[0],...,a[m-1] get lost.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: (P.Exp.derivatives() << 1).underivatives() - P.Exp  
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return FormalPowerSeries(lambda n: a[n+m],parent=a._parent)

    def __rshift__(a,m=1):
        """
        Returns the powerseries with coefficients shifted to the right by m.
        The resulting coefficients b[0],...,b[m-1] are zero.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: (P.Exp.derivatives() >> 1).underivatives() - P.Exp
        [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return FormalPowerSeries(lambda n: 0 if n<m else a[n-m],parent=a._parent)

    def diff(a,m=1): 
        """
        Differentiates the powerseries m times.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.diff(3) - P.Exp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.by_sequence([1],5).diff(5)[0] == factorial(5)
        True
        """
        def f(n):
            """ sage: None   # indirect doctest """
            if -m <= n and n < 0:
                return 0
            else:
                return a[n+m]*prod(k for k in range(n+1,n+m+1))

        def deg(v,m):
            """
            Minimal index of a[n]!=0
            """
            if v >= 0:
                return max(v-m,0)
            return v-m

        return FormalPowerSeries(f,deg(a.min_index,m),parent=a._parent)

#     def integral(a,c=0,m=1):
#         """
#         Integrates the powerseries m times with integration constant being 0
#         """
#         for i in range(-m,0):
#             if a[i] != 0:
#                 if m == 1:
#                     raise ValueError, "Coefficient -1 must be 0, but it is: " + repr(a[-1])
#                 else:
#                     raise ValueError, "Coefficients from -"+repr(m)+" upto -1 must be 0, however a[" +repr(i)+"]=" + repr(a[i])

#         def f(n):
#             if 0 <= n and n < m:
#                return c
#             return a[n-m]/prod(Integer(k) for k in range(n-m+1,n+1))
#         return a.new(f,a.min_index+m)

    def integral(a,c=0):
        """
        Integrates the powerseries with integration constant c

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P.Exp.integral(1) - P.Exp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Exp.integral(0) + P.One - P.Exp  
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """

        def f(n):
            """ sage: None   # indirect doctest """

            if n == 0:
                return c
            if n < a.min_index+1:
                return 0

            #This test can not be moved to the beginning because
            #it would break lazyness
            if a.min_index < 0:
                assert a[-1] == 0, "Coefficient at -1 must be 0, but it is: " + repr(a[-1])
            return a[n-1]/Integer(n)
            
        if c == 0:
            return a.FormalPowerSeries(f,a.min_index+1)
        else:
            return a.FormalPowerSeries(f)

    ### finite approximate operations

    def carleman_matrix(p,N,M=None):
        """
        The carleman_matrix has as nth row the coefficients of p^n.
        It has N rows and N columns, except M specifies a different number of 
        rows.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([1,1]).carleman_matrix(4) == matrix([[1,0,0,0],[1,1,0,0],[1,2,1,0],[1,3,3,1]])                      
        True
        """
        if M == None: 
            M=N
        return matrix([[p.npow(m)[n] for n in range(N) ] for m in range(M)])

    def bell_matrix(a,N,M=None):
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
        if M == None:
            M=N
        return matrix([[a.npow(n)[m] for n in range(N)] for m in range(M)])

class FPS0(FormalPowerSeries):
    """
    The formal powerseries f with f[0]==0.
    """
    def __init__(self,f=None,min_index=1,**kwargs):
        """
        Initializes this FPS0. 
        Should be called only from FormalPowerSeriesRing.

        sage: None
        """
        assert min_index >= 1
        super(FPS0,self).__init__(f,min_index,**kwargs)
        
    def __or__(a,b):
        """
        Composition (right after left): a|b.
        For documentation see: `compose'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,1,2]) | P([1,2,3])
        [1, 2, 7, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return b(a)

    def nit(a,n):
        """
        n times iteration (n times composition), n is a natural number.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P(1/(x+1)-1,x).nit(2)
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        # assert n natural number
        if not a._itMemo.has_key(n):
            res = a._parent.Id
            for k in range(n):
                res = res(a)
            a._itMemo[n] = res
        return a._itMemo[n]

    def it(a,t):
        """
        The t-th (possibly non-integer) iteration.

        It satisfies:
        a.it(0) = Id
        a.it(1) = a
        a.it(s+t) == a.it(s)(a.it(t))

        Alternative expression: a.it(t) == a & t

        See also: nit, regit (for restrictions depending t's kind)

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: P([0,2]).it(-2)              
        [0, 1/4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        a._assertp0()

        if isinstance(t,Integer) or isinstance(t,int):
            if t >= 0:
                return a.nit(t)
            return a.inv().nit(-t)
        return a.regit(t)

    def regit(a,t):
        """
        Regular (non-integer) iteration (works also for integer t).
        Preconditions: 
            a[1]**n != a[1] for all n. 
            Particularly a[1]!=0 and a[1]!=1.
            a[1]**t must be defined.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([0,2]).it(1/2)
        sage: (p[0],p[1],p[2])
        (0, sqrt(2), 0)
        """
        b = a.FPS0()
        b.min_index = 1
        def f(n):
            """ sage: None   # indirect doctest """
            if decidable0(a.K):
                assert a[1]!=1, a[1]
                assert a[1]!=0, a[1]

            #print "(" + repr(n)
            if n == 0:
                #print ")"
                return 0
            if n == 1:
                #print ")"
                return a[1]**t
            res = a[n]*(b[1]**n)-b[1]*a[n]

            for m in range(2,n):
                res += a[m]*b.npow(m)[n] - b[m]*a.npow(m)[n]

            res /= a[1]**n - a[1]
            #print ")"
            return res
        b.f = f
        return b

    def regit_b(a,t):
        """
        Regular iteration via the schroeder function.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([0,2]).regit_b(1/2)
        sage: (p[0],p[1],p[2])
        (0, sqrt(2), 0)
        """
        s = a.schroeder()
        return s.inv()(s.scalm(a[1]**t))



    def __and__(a,t):
        """
        t-th (possibly non-integer) iteration: a&t.
        For documentation see: `it'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: p = P([0,2]).it(1/2)
        sage: (p[0],p[1],p[2])
        (0, sqrt(2), 0)
        """
        
        return a.it(t)

    def __invert__(a):
        """
        The inverse: ~a.
        For documentation see: `inv'.

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: ~P.Inv_selfroot_inc.dec() - P.Selfroot_inc.dec() 
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        return a.inv()

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
        """
        a._assertp0()

        b = FPS0()
        def f(n):
            """ sage: None # indirect doctest """
            if n==0:
                return 0
            if n==1:
                return 1/a[1]
            if n>1:
                return - sum([ b[k]*a.npow(k)[n] for k in range(1,n)],a.K(0))/a[1]**n
        b.f = f
        return b


    def julia_b(a):
        """
        diff(it(a,t),t)(t=0) == ln(a[1])*julia(a)
        """
        a._assertp0()
        
        Poly=PolynomialRing(a.K,'x')
        b = FormalPowerSeriesRing(Poly)()
        b.min_index = 1

        def f(n):
            """ sage: None   # indirect doctest """
            if decidable0(a.K):
                assert a[1] != 0

            if n == 0:
                return Poly([0])
            if n == 1:
                return Poly([0,1])
            res = a[n]*(b[1]**n)-b[1]*a[n]
            res += sum([a[m]*b.npow(m)[n] - b[m]*a.npow(m)[n] for m in range(2,n)],a.K(0))
            res /= a[1]**n - a[1]
            return res
        b.f = f

        def h(p):
            """ sage: None # indirect doctest """
            return sum([p.coeffs()[n]*n for n in range(p.degree()+1)],a.K(0))

        return a.FPS0(lambda n: h(b[n]))

    def julia(a):
        """

        Precondition: a[1]**n!=a[1] for all n>1

        sage: from sage.rings.formal_powerseries import FormalPowerSeriesRing
        sage: P = FormalPowerSeriesRing(QQ)
        sage: a = P([0,2,1])               
        sage: j = a.julia_b()                   
        sage: j(a) - a.diff()*j            
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        """
        
        ap = a.diff()
        
        j = FormalPowerSeries()
        def f(n):
            """ sage: None #indirect doctest """

            if n < 0:
                return 0

            if n == 1:
                return 1
            
            r = a.K(0)

            for k in range(1,n):
                r+=ap[n-k]*j[k]

            for k in range(1,n):
                r-=j[k]*a.npow(k)[n]

            return r/(a[1]**n-a[1])
        j.f = f
        return j
            
        
    def itlog(a):
        """
        Iterative logarithm or Julia function.
        Has different equivalent definitions:
        1. Solution j of: j o a = a' * j
        2. j = diff(f.it(t),t)(t=0)

        It has similar properties like the logarithm:
        itlog(f^t) == t*itlog(f)

        It can be used to define the regular Abel function abel(f) by
        abel(f)' = 1/itlog(f)

        Refs:
        Eri Jabotinsky, Analytic iteration (1963), p 464
        Jean Ecalle, Theorie des Invariants Holomorphes (1974), p 19
        """

        #TODO this should be possible directly
        _t = var('_t')
        g = a.it(_t)
        def f(n):
            """ sage: None   # indirect doctest """
            return diff(g[n],_t)(_t=0)
        res = a.FPS0(f)
        res.min_index = res.val()
        return res

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

        q = a[1]
        s = FPS01(parent=a._parent)
        s.min_index = 1
        def f(n):
            """ sage: None   # indirect doctest """
            if decidable0(a.K):
                assert a[1] != 0, a[1]
                assert a[1] != 1, a[1]
            
            if n == 0:
                return 0
            if n == 1:
                return 1
            return sum([s[m]*a.npow(m)[n] for m in range(1,n)],a.K(0))/(q - q**n)
        s.f = f
        return s
        
    def abel(f):
        """
        The regular Abel function of a powerseries f (f[1]**n != f[1]) 
        has the form a(x)=(ln(x)+ps(x))/ln(q)
        where q=f[1]!=0,1 and ps is a powerseries
        
        This method returns ps.
        """
        f._assertp0()

        P = f._parent
        return ((f.schroeder()<<1) - P.One).reclass() | P.Log_inc

    def abel2(a):
        """
        A different implementation of the regular Abel function via
        intgeration of 1/julia(a).
        """
        
        return a.FormalPowerSeries(a.julia().rcp().f,min_index=0,complies=False).integral()


class FPS01(FPS0):
    """
    The FormalPowerSeries p with p[0]==0 and p[1]==1.
    """

    def FPS01(self,f,**kwargs):
        """
        Returns a FPS01 with the same parent as self.
        """
        return FPS01(f,parent=self._parent,**kwargs)

    def valit(a):
        """
        Returns the first index i such that f[i] != id[i]
        """
        if not a[0] == 0:
            return 0
        if not a[1] == 1:
            return 1
        n = 2
        while a[n] == 0:
            n+=1
        return n

#     def it_b(p,t):
#         """
#         A different direct implementation for `it'.

#         sage: p = P.Dec_exp.it_b(1/2)  
#         sage: (p | p) - P.Dec_exp    
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         """
#         N=p.valit()
#         P = p._parent
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
            
#         q.f = f
#         return q

    def regit(a,t):
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
        """

        def f(n):
            """ sage: None   # indirect doctest """
            if decidable0(a.K):
                assert a[0] == 0, "The index of the lowest non-zero coefficient must be 1, but is " + repr(a.min_index)
                assert a[1] == 1, "The first coefficient must be 1, but is " + repr(a[1])

            if n == 1: return 1
            #def c(m):
            #    return (-1)**(n-1-m)*binomial(t,m)*binomial(t-1-m,n-1-m)
            #res = sum([c(m)*a.nit(m)[n] for m in range(n)],a.K(0))
            #return res
            return sum([binomial(t,m)*sum([binomial(m,k)*(-1)**(m-k)*a.nit(k)[n] for k in range(m+1)],a.K(0)) for m in range(n)],a.K(0))
        return a.FPS01(f)

    def julia(a):
        """
        diff(it(a,t),t)(t=0) == ln(a[1])*julia(a)
        """
        #diff(,t)(t=0) is the first coefficient of binomial(t,m)
        #Stirling1(m)[k] is the kth coefficient of m!*binomial(t,m)
        P = a._parent
        res = P(lambda n: sum([P.Stirling1[m][1]/factorial(m)*sum([binomial(m,k)*(-1)**(m-k)*a.nit(k)[n] for k in range(m+1)],a.K(0)) for m in range(n)],a.K(0)))
        res.min_index = res.val()
        return res
        

    def abel_coeffs(a):
        """
        The Abel function a of a power series f with f[0]=0 and f[1]=1
        generally has the form
        F(z) + p(z), where
        F(z)=ji[-m]*z^{-m+1}/(-m+1)+...+ji[-2]*z^{-1}/(-1)+ji[-1]*log(z)
        and p is a powerseries (with positive indices only)

        ji[-1] is called the iterative residue (Ecalle)
        ji is the reciprocal of the Julia function
        (also called iterative logarithm) -which is meromorphic- of f

        The method returns the sequence [ji[-1],[F[-m+1],...,F[-1],p[0],p[1],p[2],...]

        These coefficients can be useful to compute the Abel function, 
        for which the powerseries is a non-converging asymptotic development.

        The Abel function can then be gained by
        lim_{n->oo} F(f&n(z))-n
        """
        
        juli = a.julia().rcp()
#         m = jul.val()
#         juli = (jul << m).rcp() 
#         return [[ juli[m+i]/(i+1) for i in range(-m,-1) ],juli[m-1], (juli<<m).integral()]
        resit = juli[-1]
        #juli[-1]=0
        return [resit,juli.set_element(-1,0).integral()]

