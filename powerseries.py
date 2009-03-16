"""
Infinite/Lazy Powerseries

Author: Henryk Trappmann
"""

from sage.structure.sage_object import SageObject
from sage.rings.arith import factorial
from sage.rings.arith import binomial
from sage.rings.integer import Integer
from sage.calculus.calculus import SymbolicExpression, SymbolicVariable, var, log
from sage.calculus.functional import diff
from sage.rings.rational_field import QQ, RationalField
from sage.rings.rational import Rational
from sage.rings.real_mpfr import RR, RealField
from sage.rings.complex_field import ComplexField_class
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.misc.misc_c import prod
from sage.rings.infinity import Infinity

def decidable0(K): 
    if K == Integer or K == int:
        return True
    if K == Rational:
        return True
    if isinstance(K,RationalField):
        return True
    #            if isinstance(K,RealField):
    #                return true
    #            if isinstance(K,ComplexField_class):
    #                return true
    return False

class PowerSeriesRingI(SageObject):
    def __call__(self,p=None,v=None,at=None):
        return PowerSeriesI(p,v,at,parent=self)

    def __init__(self,base_ring):
        if base_ring == None:
            return

        self.K = base_ring


        def PSF(f):
            return self(f)
        def PSS(seq):
            return self(seq)

        K = self.K

        self.zero = PSS([])
        self.one = PSS([K(1)])
        self.id = self([K(1)],1)
        self.inc = PSS([K(1),K(1)])
        self.dec = PSS([K(-1),K(1)])
        self.exp = PSF(lambda n: K(1/factorial(n)))
        self.log_inc = self(lambda n: K(0) if n==0 else K((-1)**(n+1)/Integer(n)),1)
        self.sin = self(lambda n: K(0) if n % 2 == 0 else K((-1)**((n-1)/2)/factorial(n)),1)
        self.cos = PSF(lambda n: K(0) if n % 2 == 1 else K((-1)**(n/2)/factorial(n)))

        def arcsin(n):
            if n % 2 == 0:
                return K(0)
            evenprod = Integer(1)
            oddprod = Integer(1)
            for k in range(2,n):
                if k % 2 == 0:
                    evenprod *= k
                else:
                    oddprod *=k
            return K(oddprod/evenprod/n)
                            
        self.arcsin = self(arcsin,1)
        self.arctan = self(lambda n: K(0) if n % 2== 0 else K((-1)**(n/2)/Integer(n)),1)

        self.sinh = self(lambda n: K(0) if n % 2 == 0 else K(1/factorial(n)),1)
        self.cosh = PSF(lambda n: K(0) if n % 2 == 1 else K(1/factorial(n)))
        def arcsinh(n):
            if n % 2 == 0:
                return K(0)
            evenprod = Integer(1)
            oddprod = Integer(1)
            for k in range(2,n):
                if k % 2 == 0:
                    evenprod *= k
                else:
                    oddprod *= k
            return K((-1)**(n/2)*oddprod/evenprod/n)
        self.arcsinh = self(arcsinh,1)
        self.arctanh = self(lambda n: K(0) if n % 2 == 0 else K(1/Integer(n)),1)

        self.bernoulli = (self.id / self.exp.dec()).derivatives()

        def tan(N):
            if N % 2 == 0:
                return K(0)
            n = (N + 1) / 2
            return K(self.bernoulli[2*n] * (-4)**n * (1-4**n) / factorial(2*n))
        self.tan = self(tan,1)

        def tanh(N):
            if N % 2 == 0:
                return K(0)
            n = (N+1)/2
            return K(self.bernoulli[2*n] * (-1)**(2*n) * 4**n * (4**n-1) / factorial(2*n))
        self.tanh = self(tanh,1)

        self.xexp = self(lambda n: K(0) if n==0 else K(1/factorial(n-1)),1)
        """ x*exp(x) """

        self.lambert_w = self(lambda n: K(0) if n==0 else K((-n)**(n-1)/factorial(n)),1)
        """ Lambert W function is the inverse of f(x)=x*e^x """

        def sqrt_inc(n):
            evenprod=Integer(1)
            oddprod=Integer(1)
            for k in range(2,2*n+1):
                if k%2 == 0:
                    evenprod *= k
                else:
                    oddprod *= k
            return K((-1)**n *oddprod/evenprod/(1-2*n))
        self.sqrt_inc = PSF(sqrt_inc)

        #dont go into a recursion defining stirling1
        if isinstance(K,PowerSeriesRingI):
            return

        self.stirling1 = PowerSeriesRingI(self)()
        def f(n):
            """
            Returns the sequence of Stirling numbers of the first kind.
            These are the coefficients of the polynomial x(x-1)(x-2)...(x-n+1).
            stirling1[n][k] is the coefficient of x^k in the above polynomial.
            """
            
            if n==0:
                res = self(lambda k: 1 if k==0 else 0)
            else:
                g = self.stirling1[n-1]
                res = self(lambda k: g[k-1]-(n-1)*g[k],1)
        
            return res
        self.stirling1.f = f

        def lehmer_comtet(n,k): #A008296
            return sum([binomial(l, k)*k^(l-k)*self.stirling1[n][l] for l in range(k,n+1)],self.K(0))
        self.A000248 = PSF(lambda n: sum([k**(n-k)*binomial(n,k) for k in range(n+1)],self.K(0)))

        #self.selfpower_inc = PSF(lambda n: K(sum([ lehmer_comtet(n,k) for k in range(0,n+1))/factorial(n),self.K(0)))
        self.selfpower_inc = PSF(lambda n: K(sum([ self.stirling1[n][k]*self.A000248[k] for k in range(n+1)],self.K(0))/factorial(n)))
        """
        Power series of x^x at 1
        """
        self.superroot_inc = PSF(lambda n: K(sum([ self.stirling1[n][k]*Integer(1-k)**(k-1) for k in range(n+1)],self.K(0))/factorial(n)))
        """
        Powerseries of the inverse of x^x developed at 1.
        """

        def A003725(n):
            """
            Derivatives of exp(x*e^(-x)) at 0
            """
            return K(sum([ (-k)**(n-k)*binomial(n, k) for k in range(n+1)],self.K(0)))
        self.A003725 = PSF(A003725)

        self.selfroot_inc = PSF(lambda n: K(sum([ self.stirling1[n][k]*self.A003725[k] for k in range(n+1)],self.K(0))/factorial(n)))
        """
        Development of x^(1/x) at 1
        """

        self.inv_selfroot_inc = PSF(lambda n: K(sum([self.stirling1[n][k]*K((k+1))**(k-1) for k in range(n+1)],self.K(0))/factorial(n)))
        """
        The inverse of the self root x^(1/x) at 1.
        The power series at 1, that computes the fixed point of b^x
        for given b as variable of the power series.
        """

    def _repr_(self):
        return "Infinite Lazy/Cached Power Series over " + repr(self.K)

    def base_ring(self):
        return self.K

    #does not really belong to a powerseries package but there is currently no
    #other place for it
    def msexp(self,n,digits):
        #sexp(z)=exp^z(1)=exp^{z+1}(0)
        x=var('x')
        sexp = self.exp.it_matrixpower(x+1,n,RealField(digits))[0]
        return lambda z: sexp(x=z)

    def _test(self):
        """
        sage: from hyperops.powerseries import *
        sage: P = PowerSeriesRingI(QQ)
        
        sage: P.exp
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        sage: P.log_inc
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        sage: P.sin
        [0, 1, 0, -1/6, 0, 1/120, 0, -1/5040, 0, 1/362880, 0, -1/39916800, 0, ...]
        sage: P.cos
        [1, 0, -1/2, 0, 1/24, 0, -1/720, 0, 1/40320, 0, -1/3628800, 0, 1/479001600, ...]
        sage: P.arcsin
        [0, 1, 0, 1/6, 0, 3/40, 0, 5/112, 0, 35/1152, 0, 63/2816, 0, 231/13312, 0, ...]
        sage: P.arctan
        [0, 1, 0, -1/3, 0, 1/5, 0, -1/7, 0, 1/9, 0, -1/11, 0, 1/13, 0, -1/15, 0, ...]
        sage: P.sinh
        [0, 1, 0, 1/6, 0, 1/120, 0, 1/5040, 0, 1/362880, 0, 1/39916800, 0, ...]
        sage: P.cosh
        [1, 0, 1/2, 0, 1/24, 0, 1/720, 0, 1/40320, 0, 1/3628800, 0, 1/479001600, 0, ...]
        sage: P.arcsinh
        [0, 1, 0, -1/6, 0, 3/40, 0, -5/112, 0, 35/1152, 0, -63/2816, 0, 231/13312, ...]
        sage: P.arctanh
        [0, 1, 0, 1/3, 0, 1/5, 0, 1/7, 0, 1/9, 0, 1/11, 0, 1/13, 0, 1/15, 0, 1/17, ...]
        sage: P.bernoulli
        [1, -1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, ...]
        sage: P.tan
        [0, 1, 0, 1/3, 0, 2/15, 0, 17/315, 0, 62/2835, 0, 1382/155925, 0, ...]
        sage: P.tanh
        [0, 1, 0, -1/3, 0, 2/15, 0, -17/315, 0, 62/2835, 0, -1382/155925, 0, ...]
        sage: P.sqrt_inc
        [1, 1/2, -1/8, 1/16, -5/128, 7/256, -21/1024, 33/2048, -429/32768, ...]
        sage: P.lambert_w
        [0, 1, -1, 3/2, -8/3, 125/24, -54/5, 16807/720, -16384/315, 531441/4480, ...]
        sage: P.selfpower_inc
        [1, 1, 1, 1/2, 1/3, 1/12, 3/40, -1/120, 59/2520, -71/5040, 131/10080, ...]
        sage: P.superroot_inc
        [1, 1, -1, 3/2, -17/6, 37/6, -1759/120, 13279/360, -97283/1008, ...]
        sage: P.A003725
        [1, 1, -1, -2, 9, -4, -95, 414, 49, -10088, 55521, -13870, -2024759, ...]
        sage: P.selfroot_inc
        [1, 1, -1, 1/2, 1/6, -3/4, 131/120, -9/8, 1087/1260, -271/720, -2291/10080, ...]
        sage: P.inv_selfroot_inc
        [1, 1, 1, 3/2, 7/3, 4, 283/40, 4681/360, 123101/5040, 118001/2520, ...]


#         #takes too long:
#         sage: P(exp(x),x)-P.exp
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(log(x+1),x) - P.log_inc
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(cos(x),x)-P.cos
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(sin(x),x)-P.sin
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arcsin(x),x) - P.arcsin
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arctan(x),x) - P.arctan
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(sinh(x),x)-P.sinh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(cosh(x),x)-P.cosh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arcsinh(x),x)-P.arcsinh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(arctanh(x),x)-P.arctanh
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(sqrt(x+1),x)-P.sqrt_inc
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(x*exp(x),x)-P.xexp
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
#         sage: P(exp(x)-1,x)-P.exp.dec()
#         [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: P.log_inc | P.exp.dec()
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.arcsin | P.sin      
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.arctan | P.tan
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.arctanh | P.tanh
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.lambert_w | P.xexp
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.selfpower_inc | P.superroot_inc.dec()
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.selfroot_inc | P.inv_selfroot_inc.dec()           
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: P.superroot_inc ** P.superroot_inc
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.tan - P.sin / P.cos
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.sin*P.sin + P.cos*P.cos
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
        sage: (p << 1).log().smul(a[0]) + (a[1] | p) - a[1]
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: a = var('a')
        sage: p = PowerSeriesRingI(PolynomialRing(QQ,a))(exp(a*x)-1,x)
        sage: pah = p.abel_npar()
        sage: pac = p.abel_npar2()
        sage: pah
        [0, 1/2*a/(-a + 1), (5/24*a^3 + 1/24*a^2)/(a^3 - a^2 - a + 1), ...]
        sage: pac
        [0, -1/2*a/(a - 1), (5/12*a^3 + 1/12*a^2)/(2*a^3 - 2*a^2 - 2*a + 2), ...]
        sage: [pac[k] - pah[k]==0 for k in range(0,5)]
        [True, True, True, True, True]
        """
        pass

class PowerSeriesI(SageObject):
    """
    Infinite cached/lazy power series:

    A powerseries p is basically seen as an infinite sequence of coefficients
    The n-th coefficient is retrieved by p[n].

    EXAMPLES:
        sage: from hyperops.powerseries import PowerSeriesRingI
        sage: PQ = PowerSeriesRingI(QQ)
        sage: #Predefined PowerSeries                                                         
        sage: expps = PQ.exp
        sage: expps.poly(10,x)
        1/362880*x^9 + 1/40320*x^8 + 1/5040*x^7 + 1/720*x^6 + 1/120*x^5 + 1/24*x^4 + 1/6*x^3 + 1/2*x^2 + x + 1
        sage: expps
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        sage: PQ.zero
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ.one
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PQ.id
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: #finite powerseries                                                             
        sage: p = PQ([1,2,3,4])
        sage: p.poly(10,x)
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
        sage: dexp = expps - one
        sage: expps.o(dexp)
        [1, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]

        sage: #we come into interesting regions ...                                           
        sage: dexp.o(dexp)
        [0, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]
        sage: dexp.nit(2)
        [0, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]
        sage: dexp.it(-1)
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        sage: dexp.it(-1).o(dexp)
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: hdexp = dexp.it(1/2)
        sage: hdexp
        [0, 1, 1/4, 1/48, 0, 1/3840, -7/92160, 1/645120, 53/3440640, -281/30965760, ...]
        sage: #verifying that shoudl be Zero                                                  
        sage: hdexp.it(2) - dexp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: #symbolic (parabolic) iteration                                                 
        sage: dexp.it(x)
        [0, 1, x/2, 5*(x - 1)*x/12 - (x - 2)*x/6, ...]
        sage: q = dexp.it(1/x).it(x)
        sage: q[3]
        (5*(1/x - 1)/(6*x) - (1/x - 2)/(3*x) + 1/(2*x^2))*(x - 1)*x/2 - (5*(1/x - 1)/(12*x) - (1/x - 2)/(6*x))*(x - 2)*x
        sage: #simiplify and compare                                                          
        sage: expand(q[3])
        1/6
        sage: dexp[3]
        1/6

        sage: #you can initialize power series with arbitrary functions on natural numbers    
        sage: #for example the power series of sqrt(2)^x can be given as                      
        sage: bsrt = PowerSeriesRingI(SR)(sqrt(2)^x,x)

        sage: #making the 0-th coefficient 0 to get the decremented exponential   
        sage: dbsrt = bsrt.set_index(0,0)
        
        sage: #and now starting hyperbolic iteration                                          
        sage: dbsrt2 = dbsrt.it(x).it(1/x)
        sage: #Sage is not able to simplify                                                   
        sage: simplify(dbsrt2[3])
        (log(2)^3*(log(2)^(x + 2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)*2^x) - log(2)^3*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(8*(log(2)^2/4 - log(2)/2)) - log(2)^(x + 3)*2^(-x - 4)/3 + log(2)^(3*x + 3)*2^(-3*x - 4)/3)/(8*(log(2)^3/8 - log(2)/2)) - log(2)*(log(2)^(x + 2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)*2^x) - log(2)^3*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(8*(log(2)^2/4 - log(2)/2)) - log(2)^(x + 3)*2^(-x - 4)/3 + log(2)^(3*x + 3)*2^(-3*x - 4)/3)/(2*(log(2)^3/8 - log(2)/2)) - 2*log(2)^x*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))*(log(2)^2*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)) - log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(2*(log(2)^2/4 - log(2)/2)))/((log(2)^2/4 - log(2)/2)*2^x*(log(2)^(2*x)/2^(2*x) - log(2)^x/2^x)) + log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))*(log(2)^2*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)) - log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(2*(log(2)^2/4 - log(2)/2)))/((log(2)^2/4 - log(2)/2)*(log(2)^(2*x)/2^(2*x) - log(2)^x/2^x)))/(log(2)^(3*x)/2^(3*x) - log(2)^x/2^x)
        sage: #but numerically we can verify equality                                         
        sage: RR(dbsrt2[3](x=0.73)-dbsrt[3])
        -8.67361737988404e-19
    """

    def __init__(self,p=None,v=None,at=None,base_ring=None,parent=None):
        """
        Initialization by finite sequence of coefficients:
        Examples:
        sage: from hyperops.powerseries import PowerSeriesRingI
        sage: PQ = PowerSeriesRingI(QQ)
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
        
        """
        
        self._parent = parent
        if parent == None:
            if base_ring==None:
                self._parent = PowerSeriesRingI(QQ)
            else:
                self._parent = PowerSeriesRingI(base_ring)

        self._val = 0 #the minimal non-zero index
        self._memo = {}
        self._max_degree = Infinity
        self._powMemo = {}
        self._itMemo = {}

        self.K = self._parent.K
        
        if isinstance(p,Integer) or isinstance(p,int) or isinstance(p,Rational):
            def f(n):
                if n < 0:
                    return self.K(0)
                if n > 0:
                    return self.K(0)
                return self.K(p)
            self.f = f
            self._max_degree = 0
            return

        if isinstance(p,list):
            if v == None:
                v = 0

            l = len(p)
            self._max_degree = v+l-1
            for n in range(l):
                if p[n] != 0:
                    self._val = v+n
                    break

            def f(n):
                if n<self._val or n>self._max_degree:
                    return self.K(0)
                return p[n-v]

            self.f = f
            return

        if isinstance(p,SymbolicExpression):
            assert not v == None
            expr=p
            assert isinstance(v,SymbolicVariable)
            if at == None:
                at = 0

            def f(n):
                #too slow
                #if not at == 0 and n==0:
                #    return expr({v:at})-at
                #return simplify(diff(expr,v,n).substitute({v:at})/factorial(n))
                return self.K(expr.taylor(v,at,n).substitute({v:v+at}).coeff(v,n))

            #coeffs always returns non-empty list, at least [0,0] is contained
            self._val = expr.taylor(v,at,2).substitute({v:v+at}).coeffs(v)[0][1]
            self.f = f
            return

        if type(p) is type(lambda n: 0):
            if v == None:
                v = 0

            if decidable0(self.K):
                for n in range(v,2):
                    if p(n)!= 0:
                        v = n
                        break

            self._val=v

            if at != None:
                self._max_degree = at
            
            self.f = lambda n: p(n) if n >= self._val else self.K(0)

    def base_ring(self):
        return self._parent.K

    def __getitem__(self,n): # []
        if not self._memo.has_key(n):
            #self._memo[n] = simplify(expand(self.f(n)))
            self._memo[n] = self.f(n)
        return self._memo[n]

    def __getslice__(self,i,j): # [i:j]
        return [self[k] for k in range(i,j)]

    def set_index(a, index, value):
        """
        Returns the powerseries that has a[index] replaced by value.
        """
        return a._parent(lambda n: value if n == index else a[n],a._val)

    def set_slice(a, i, j, seq):
        """
        Returns the powerseries that has a[i:j] replaced by seq.
        """
        return a._parent(lambda n: seq[n-i] if i<=n and n<j else a[n],a._val)

    def derivatives(a):
        """
        The sequence of derivatives a[n]*n! of the powerseries a
        """
        return a._parent(lambda n: a[n]*a.K(factorial(n)))

    def underivatives(a):
        """
        Returns the sequence a[n]/n!.
        """
        return a._parent(lambda n: a[n]/a.K(factorial(n)))

    def inc(a):
        """
        Increment: a + 1
        """
        return a._parent(lambda n: a[0]+a.K(1) if n==0 else a[n])

    def dec(a):
        """
        Decrement: a-1
        """
        return a._parent(lambda n: a[0]-a.K(1) if n==0 else a[n])

    def smul(a,s):
        """
        Scalar multiplication with scalar s
        """
        return a._parent(lambda n: a[n]*s,a._val,a._max_degree)

    def __add__(a,b): # +
        """
        Addition:
        """
        def f(n):
            if n < a._val:
                if n < b._val:
                    return 0
                return b[n]
            if n < b._val:
                return a[n]
            return a[n]+b[n]
        return a._parent(f,min(a._val,b._val),max(a._max_degree,b._max_degree))

    def plus(a,b):
        """
        a.plus(b) == a+b
        """
        return a+b

    def __sub__(a,b): # -
        """
        Subtraction:
        """
        def f(n):
            if n < a._val:
                if n < b._val:
                    return 0
                #a[0]==0
                return b[n]
            if n < b._val:
                #b[0]==0
                return a[n]
            return a[n]-b[n]
        return a._parent(f,min(a._val,b._val),max(a._max_degree,b._max_degree))

    def minus(a,b):
        """
        a.minus(b) == a-b
        """
        return a-b

    def __mul__(a,b): # *
        """
        Multiplication of two powerseries.
        """
        #multiplication of two powerseries
        #this a lazy algorithm: 
        #for initial 0 in a[k] and initial 0 in b[n-k] the corresponding b[n-k] or a[k] is not evaluated
        def f(n):
            return sum([a[k]*b[n-k] for k in range(a._val,n+1-b._val)],a.K(0))
        return a._parent(f,a._val+b._val,a._max_degree+b._max_degree)

    def times(a,b):
        """
        a.times(b) == a*b
        """
        return a*b

    def __div__(c,b): # /
        """
        Division: a/b*b=a, a*b/b=a
        """
        a = c._parent()
        a._val = c._val - b._val
        a._max_degree = Infinity #maybe becomes a polynomial, maybe not
        def f(n):
            if n<c._val-b._val:
                return 0
            return (c[n+b._val] - sum([a[k]*b[n+b._val-k] for k in range(a._val,n)],c.K(0)))/b[b._val]
        a.f = f
        return a

    def rcp(a):
        return a._parent(1)/a

    def by(a,b):
        """
        a.by(b) == a/b
        """
        return a/b

    def __pow__(a,t): # **
        return a.pow(t)

    def npow(a,n):
        """
        Power for natural exponent.
        """
        if (not isinstance(n,Integer) and not isinstance(n,int)) or n<0:
            raise TypeError, type(n)
        if not a._powMemo.has_key(n):
            if n==0:
                res = a._parent.one
            elif n==1:
                res = a
            else:
                res = a.npow(n-1) * a
            a._powMemo[n] = res
        return a._powMemo[n]

    def pow(a,t):
        """
        Power for exponent being an arbitrary number or powerseries, including -1 which is rcp.
        """

        if isinstance(t,PowerSeriesI):
            P = a._parent
            return P.exp | ( a.log() * t )
        if isinstance(t,Integer) or isinstance(t,int):
            if t >= 0:
                return a.npow(t)
            return a.rcp().npow(-t)
        return a.pow_ni(t)

    def pow_ni(a,t):
        """
        Non-integer power.
        """
        if decidable0(a.K):
            assert a[0] != 0, "0th coefficient is " + repr(a[0]) + ", but must be non-zero for non-integer powers"

        da = a.set_index(0,0)

        def f(n):
            return sum([binomial(t,k) * a[0]**(t-k) * da.npow(k)[n] for k in range(n+1)],a.K(0))
        return a._parent(f)
        
    def sqrt(a):
        return a.pow_ni(1/2)

    def rt(a,n):
        return a.pow_ni(1/n)

    def log(a):
        """
        Logarithm of powerseries a with a[0]==1.
        """

        P = a._parent
        if decidable0(a.K):
            assert a[0] == 1

        dec_a = P(lambda n: 0 if n==0 else a[n])

        return P.log_inc | dec_a
    
    def nit(a,n):
        """
        n times iteration (n times composition), n is a natural number
        """
        # assert n natural number
        if not a._itMemo.has_key(n):
            res = a._parent.id
            for k in range(n):
                res = res.o(a)
            a._itMemo[n] = res
        return a._itMemo[n]

    def __xor__(a,t): # ^
        #Not recognized as it seems to be mapped to ** in sage
        return NotImplemented

    def __and__(a,t): # &
        """
        p&t is the same as p.it(t)
        """
        
        return a.it(t)

    def __or__(a,b): # |
        """
        p|q is the same as p.o(b)
        """
        return a.o(b)

    def apply(a,b):
        """
        a.apply(b) is the same as b | a
        """
        return b.o(a)

    def o(a,b):
        """
        Composition: f.o(g).poly(m*n,x) == f.poly(m,g.poly(n,x)) 
        """
        if decidable0(b.K) and b[0] != 0:
            raise ValueError, "0th coefficient of b must be 0 but is " + repr(b[0])
        def f(n):
            res = sum([a[k]*(b.npow(k)[n]) for k in range(n+1)],a.K(0))
            if a._val < 0:
                bi = b.rcp()
                res += sum([a[k]*(bi.npow(-k)[n]) for k in range(a._val,0)],a.K(0))
            return res
        return a._parent(f,a._val*b._val)

    def bell(a,n,k):
        """
        Returns the Bell polynomial of the sequence of variables a.
        """
        return derivatives(underivatives(a)**k).smul(1/factorial(k))
        

    def inv(a):
        """
        Inverse: f.inv().o(f)=Id
        """
        if decidable0(a.K) and a[0] != 0:
            raise ValueError, "0th coefficient of a must be 0 but is " + repr(a[0])
        return a.it(-1)


    def poly(a,n,x=None):
        """
        Returns the associated polynomial for the first n coefficients.
        f_0 + f_1*x + f_2*x^2 + ... + f_{n-1}*x^{n-1}
        With second argument you get the polynomial as expression in that
        variable.
        Without second argument you the get polynomial as function.
        """
        if x == None:
            return lambda x: sum([a[k]*x**k for k in range(n)],a.K(0))
        else:
            return PolynomialRing(a.K,x)(sum([a[k]*x**k for k in range(n)],a.K(0)))

    def _repr_(a):
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
        res = "["
        if a._val < 0:
            for k in range(a._val,0):
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
        r = abs(a[N])**(-1/Integer(N))
        l = r/sqrt(2.0)
        f = a.poly(N)
        x0=real(fp)
        y0=imag(fp)
        return contour_plot(lambda x,y: real(f(CC(x+i*y-fp))),(x0-l,x0+l),(y0-l,y0+l),fill=false) + contour_plot(lambda x,y: imag(f(CC(x+i*y-fp))),(x0-l,x0+l),(y0-l,y0+l),fill=false)       
                    
    def it(a,t):
        if decidable0(a.K) and a[0] != 0:
            raise ValueError, "0th coefficient of b must be 0"
        if a[1] == 1: return a.it_par(t)
        else: return a.it_npar(t)

    def it_npar(a,t):
        """
        Regular iteration at fixed point 0 for f'(0)!=1 (non-parabolic).
        """
        if decidable0(a.K):
            assert a[0]==0 and a[1]!=1

        b = a._parent()
        b._val = 1
        def f(n):
            #print "(" + repr(n)
            if n == 0:
                #print ")"
                return 0
            if n == 1:
                #print ")"
                return a[1]**t
            res = a[n]*(b[1]**n)-b[1]*a[n]
            res += sum([a[m]*b.npow(m)[n] - b[m]*a.npow(m)[n] for m in range(2,n)],a.K(0))
            res /= a[1]**n - a[1]
            #print ")"
            return res
        b.f = f
        return b

    def julia_npar(a):
        """
        diff(it_npar(a,t),t)(t=0) = ln(a[1])*julia_npar(a)
        """
        if decidable0(a.K):
            assert a[0] == 0
            assert a[1] != 0
        
        Poly=PolynomialRing(a.K,'x')
        b = PowerSeriesRingI(Poly)()
        b._val = 1

        def f(n):
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
            return sum([p.coeffs()[n]*n for n in range(p.degree()+1)],a.K(0))

        return a._parent(lambda n: h(b[n]),1)
        

    def it_par0(p,t):
        N=p.valit()
        P = p._parent
        q = P()
        def f(n):
            if n < N:
                return P.id[n]
            if n == N:
                return t * p[N]
            if n > N:
                r=p[n]
                r+=sum([p[m]*(q**m)[n] - q[m]*(p**m)[n] for m in range(N,n)])
                return r
            
        q.f = f
        return q

    def it_par(a,t):
        """
        Parabolic t-times iteration, i.e. for the case a[0]==0 and a[1]==1
        """

        if decidable0(a.K):
            assert a[0] == 0, "The index of the lowest non-zero coefficient must be 1, but is " + repr(a._val)
            assert a[1] == 1, "The first coefficient must be 1, but is " + repr(a[1])
            
        def f(n):
            if n == 1: return 1
            def c(m):
                return (-1)**(n-1-m)*binomial(t,m)*binomial(t-1-m,n-1-m)
            res = sum([c(m)*a.nit(m)[n] for m in range(n)],a.K(0))
            return res
        return a._parent(f,1)

    def it_par2(a,t):
        if decidable0(a.K):
            assert a[0] == 0
            assert a[1] == 1

        def f(n):
            return sum([binomial(t,m)*sum([binomial(m,k)*(-1)**(m-k)*a.nit(k)[n] for k in range(m+1)],a.K(0)) for m in range(n)],a.K(0))
        return a._parent(f,1)

    def julia_par(a):
        #diff(,t)(t=0) is the first coefficient of binomial(t,m)
        #stirling1(m)[k] is the kth coefficient of m!*binomial(t,m)
        P = a._parent
        res = P(lambda n: sum([P.stirling1[m][1]/factorial(m)*sum([binomial(m,k)*(-1)**(m-k)*a.nit(k)[n] for k in range(m+1)],a.K(0)) for m in range(n)],a.K(0)))
        res._val = res.val()
        return res
        

    def julia(a):
        if decidable0(a.K):
            assert a[0] == 0

            if a[1] == 1:
                return a.julia_par()
            else:
                return a.julia_npar()

        assert decidable0(a.K)

    def schroeder_npar(a):
        """
        Returns the Schroeder powerseries s with s[1]=1
        for a powerseries a with a[0]=0 and a[1]^n!=a[1] for all n

        The Schroeder powerseries s is determined up to a multiplicative
        constant by the functional equation:
        s(a(z))=a[1]*s(z)
        """
        if decidable0(a.K) and a[0] != 0:
            raise ValueError, "0th coefficient "+a[0]+" must be 0"
        if decidable0(a.K) and a[1] == 0:
            raise ValueError, "1st coefficient "+a[1]+" must be nonequal 0"
        if decidable0(a.K) and a[1] == 1:
            raise ValueError, "1st coefficient "+a[1]+" must be nonequal 1"

        q = a[1]
        s = a._parent()
        s._val = 1
        def f(n):
            if n == 0:
                return 0
            if n == 1:
                return 1
            return sum([s[m]*a.npow(m)[n] for m in range(1,n)],a.K(0))/(q - q**n)
        s.f = f
        return s
        
    def abel_npar(f):
        """
        The regular Abel function of a hyperbolic powerseries f has the form
        a(x)=(ln(x)+ps(x))/ln(q)
        where q=f[1]!=0,1 and ps is a powerseries
        
        This method returns ps
        """
        P = f._parent
        return P.log_inc | ((f.schroeder_npar()<<1) - P.one)

    def abel_npar2(a):
        return a._parent(a.julia_npar().rcp().f,0).integral()
        
    def val(a):
        """
        Returns the first index i such that f[i] != 0
        """
        n = 0
        while a[n] == 0:
            n += 1
        return n

    def valit(a):
        """
        Returns the first index i such that f[i] != Id[i]
        """
        if not a[0] == 0:
            return 0
        if not a[1] == 1:
            return 1
        n = 2
        while a[n] == 0:
            n+=1
        return n

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
        
        juli = a.julia_par().rcp()
#         m = jul.val()
#         juli = (jul << m).rcp() 
#         return [[ juli[m+i]/(i+1) for i in range(-m,-1) ],juli[m-1], (juli<<m).integral()]
        resit = juli[-1]
        #juli[-1]=0
        return [resit,juli.set_index(-1,0).integral()]

    def __lshift__(a,m=1):
        return a._parent(lambda n: a[n+m])

    def __rshift__(a,m=1):
        return a._parent(lambda n: 0 if n<m else a[n-m])

    def diff(a,m=1): 
        """
        Differentiates the powerseries m times.
        """
        def f(n):
            if -m <= n and n < 0:
                return 0
            else:
                return a[n+m]*prod(k for k in range(n+1,n+m+1))

        def deg(v,m):
            if v >= 0:
                return max(v-m,0)
            return v-m

        return a._parent(f,deg(a._val,m),deg(a._max_degree,m))

    def integral(a,m=1):
        """
        Integrates the powerseries m times with integration constant being 0
        """
        for i in range(-m,0):
            if a[i] != 0:
                if m == 1:
                    raise ValueError, "Coefficient -1 must be 0, but it is: " + repr(a[-1])
                else:
                    raise ValueError, "Coefficients from -"+repr(m)+" upto -1 must be 0, however a[" +repr(i)+"]=" + repr(a[i])

        def f(n):
            if 0 <= n and n < m:
               return 0
            return a[n-m]/prod(Integer(k) for k in range(n-m+1,n+1))
        return a._parent(f,a._val+m,a._max_degree+m)

    def ilog(a):
        """
        Iterative logarithm:
        ilog(f^t) == t*ilog(f)
        defined by: diff(f.it(t),t)(t=0)
        can be used to define the regular Abel function abel(f) by
        abel(f)' = 1/ilog(f)

        Refs:
        Eri Jabotinsky, Analytic iteration (1963), p 464
        Jean Ecalle, Theorie des Invariants Holomorphes (1974), p 19
        """

        #TODO this should be possible directly
        _t = var('_t')
        g = a.it(_t)
        def f(n):
           return diff(g[n],_t)(_t=0)
        res = a._parent(f)
        res._val = res.val()
        return res

    ### finite approximate operations

    def carleman_matrix(p,M,N=None):
        """
        The carleman_matrix has as nth row the coefficients of p^n
        It has M rows and M columns, except N specifies a different number of 
        columns.
        """
        if N == None: 
            N=M
        return matrix([[p.npow(m)[n] for n in range(N) ] for m in range(M)])

    def bell_matrix(a,M,N=None):
        """
        The Bell matrix with M rows and M (or N) columns of this power series.
        The m-th column of the Bell matrix (starting to count with m=0)
        is the sequence of coefficients of the m-th power of the power series.
        The Bell matrix is the transpose of the Carleman matrix.
        """
        if N == None:
            N=M
        return matrix([[a.npow(n)[m] for n in range(N)] for m in range(M)])

    def it_matrixpower(p,t,n,root_field=RR):
        """
        t times Iteration via matrix power. t is a complex number.
        This method can also iterate power series with p[0]!=0.
        It is identical with the regular iteration for the case p[0]==0.
        However in the case p[0]!=0 it is no finite operation anymore and
        hence requires the size n of the Carleman matrix to use.
        This matrix which has the coefficients of p in its first row
        is raised to the t-th power and then the coefficients 
        of the first row are returned.

        Works currently only if the eigenvalues are all different.
        """
        assert n>=2, "Carleman matrix must at least be of size 2 to retrieve the coefficients. But given was " + repr(n)
        CM = p.carleman_matrix(n)
        ev = CM.charpoly().roots(root_field)
        assert len(ev) == n, "Carleman matrix must have exactly " + repr(n) + "eigenvalues, but has " + repr(len(ev))
    
        Char = [0]*n
        for k in range(n):
            #here is possibility for improvement of precision
            #to separate the fractional from the root parts
            #expanding the product
            Char[k] = CM - ev[k][0]*identity_matrix(n)
    
        #we want to have the first row of the product of the matrices
        #thatswhy we mulitply in front with:
        prod = vector(p.K,[0,1]+[0]*(n-2))
        prodwo = [0]*n
        for k in range(n):
            prodwo[k]=prod #these are the first terms until k-1
    
            #no need to continue
            if k == n-1:
                break
    
            #and we add the terms starting with k+1
            for i in range(k+1,n):
                prodwo[k] = prodwo[k] * Char[i]
    
            prod = prod * Char[k]
    
        sprodwo = [0]*n
        for k in range(n):
            if k==0:
                sprodwo[k] = ev[k][0] - ev[1][0]
                start = 2
            else:
                sprodwo[k] = ev[k][0] - ev[0][0]
                start = 1
    
            for i in range(start,n):
                if i != k:
                    sprodwo[k] = sprodwo[k] * (ev[k][0] - ev[i][0])
    
        res = ev[0][0]**t/sprodwo[0] * prodwo[0]
        for k in range(1,n):
            res += ev[k][0]**t/sprodwo[k]*prodwo[k]
    
        return res.list()

    def sexp(p,n,res_field=RR):
        """
        t times Iteration via matrix power. t is a complex number.
        This method can also iterate power series with p[0]!=0.
        It is identical with the regular iteration for the case p[0]==0.
        However in the case p[0]!=0 it is no finite operation anymore and
        hence requires the size n of the Carleman matrix to use.
        This matrix which has the coefficients of p in its first row
        is raised to the t-th power and then the coefficients 
        of the first row are returned.

        Works currently only if the eigenvalues are all different.
        """
        assert n>=2, "Carleman matrix must at least be of size 2 to retrieve the coefficients. But given was " + repr(n)
        CM = p.carleman_matrix(n)
        ev = [ r[0] for r in CM.charpoly().roots(QQbar) ]
        assert len(ev) == n, "Carleman matrix must have exactly " + repr(n) + "eigenvalues, but has " + repr(len(ev))
    
        #We want to compute:
        #sum over k: evk^t*(CM-ev1*I)*(CM-ev2*I)*. omit k * (CM-evn*I)/(evk-ev1)*.. omit k *(evk-evn)
        Char = [0]*n
        for k in range(n):
            #here is possibility for improvement of precision
            #to separate the fractional from the root parts
            #expanding the product
            Char[k] = CM - ev[k]*identity_matrix(n)
    
        #we want to have the first row of the product of the matrices
        #thatswhy we mulitply in front with:
        prod = vector(QQbar,[0,1]+[0]*(n-2))
        prodwo = [0]*n
        for k in range(n):
            prodwo[k]=prod #these are the first terms until k-1
    
            #no need to continue
            if k == n-1:
                break
    
            #and we add the terms starting with k+1
            for i in range(k+1,n):
                prodwo[k] = prodwo[k] * Char[i]
    
            prod = prod * Char[k]
    
        sprodwo = [0]*n
        for k in range(n):
            if k==0:
                sprodwo[k] = ev[k] - ev[1]
                start = 2
            else:
                sprodwo[k] = ev[k] - ev[0]
                start = 1
    
            for i in range(start,n):
                if i != k:
                    sprodwo[k] = sprodwo[k] * (ev[k] - ev[i])
    
        for k in range(n):
            print ev[k]
            print prodwo[k][0]/sprodwo[k]
            print res_field
        #return lambda t: sum(res_field(ev[k])**t*res_field(prodwo[k][0]/sprodwo[k]) for k in range(n))
        return [ev,[prodwo[k][0]/sprodwo[k] for k in range(n)]]

    def natural_abel_seq(p,n):
        """
        Returns the first n coefficients of the natural Abel power sequence,
        obtained from an nxn Carleman/Bell matrix.
        This method does not work for p[0]=0.
        """
        assert n>=2, "Carleman matrix must at least be of size 2 to retrieve the coefficients."
        B=p.carleman_matrix(n)-diagonal_matrix([1]*(n))
        x=B[range(1,n),range(n-1)].solve_left(matrix([[1] + [0]*(n-2)]))
        return [-1]+x[0].list()


#     #static methods
#     def Exp(self):
#         return PowerSeriesI(lambda n: self.K(1)/self.K(factorial(n)))
# 
#     def Log_inc(self):
#         return PowerSeriesI(lambda n: 0 if n==0 else (self.K((-1)**(n+1)))/self.K(n))
# 
#     def Sin(self):
#         def c(n):
#             if n % 2 == 0:
#                 return 0
#             return self.K((-1)**(n/2))/self.K(factorial(n))
#         return PowerSeriesI(c)
# 
#     def Cos(self):
#         def c(n):
#             if n % 2 == 1:
#                 return 0
#             return self.K((-1)**(n/2))/self.K(factorial(n))
#         return PowerSeriesI(c)
# 
#     def LambertW(self):
#         """
#         Lambert W function is the inverse of f(x)=x*e^x
#         """
#         return PowerSeriesI(lambda n: 0 if n==0 else (-n)**(n-1)/factorial(n))
# 
#     def Xexp(self):
#         """
#         x*exp(x)
#         """
#         return PowerSeriesI(lambda n: 0 if n==0 else 1/factorial(n-1))
# 
#     
#     def Dec_exp(self):
#         """
#         exp(x)-1
#         """
#         return PowerSeriesI(lambda n: 0 if n==0 else 1/factorial(n))
# 
#     def Stirling1(self,n):
#         """
#         Stirling numbers of the first kind
#         """
#         try:
#             _stirling_memo
#         except NameError:
#             _stirling_memo = {}
# 
#         if _stirling_memo.has_key(n):
#             return _stirling_memo[n]
# 
#         def f(k):
#             if n==0:
#                 if k==0:
#                     return 1
#                 return 0
#             g = self.Stirling1(n-1)
#             return g[k-1]-(n-1)*g[k]
# 
#         res = PowerSeriesI(f)
# 
#         _stirling_memo[n] = res
#         return res
#                 
#     def inv_selfroot_inc(self):
#         """
#         The power series at 1, that computes the fixed point of b^x
#         for given b as variable of the power series.
#         """
#         def c(n,k):
#             if k==0:
#                 return self.Stirling1(n)[k]
#             #print n,k,(k+1)**(k-1),self.Stirling1(n)[k]
#             return self.Stirling1(n)[k]*(k+1)**(k-1)
#         def f(n):
#             if n==0:
#                 return 0
#             return sum([ c(n,k) for k in range(n+1)])/factorial(n)
#         return PowerSeriesI(f)
# 
#     def Id(self):
#         return PowerSeriesI([0,1])
#     
#     def One(self):
#         return PowerSeriesI([1])
# 
#     def Zero(self):
#         return PowerSeriesI([])
# 

