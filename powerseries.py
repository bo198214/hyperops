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
    def ps(self,f,min_index,T=None):
        if T == None:
            if not decidable0(self.K):
                return PowerSeriesI(f,parent=self)
#                raise TypeError, "Can not decide type of powerseries, please specify with T="
            if f(0) == self.K0 and f(1) == self.K1:
                return PS01(f,parent=self)
            else:
                return PowerSeriesI(f,parent=self)
        return T(f,parent=self)

    def byUndefined(self,T=None):
        if T==None:
            return PowerSeriesI()
        return T()
    
    def byLambda(self,f,min_index=0,**kwargs):
#          if decidable0(self.K):
#              for n in range(v,2):
#                  if p(n)!= 0:
#                      v = n
#                      break

        return self.ps(lambda n: f(n) if n >= min_index else self.K0,min_index,**kwargs)
        
    def byList(self,list,min_index=0,**kwargs):
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

        start = min_index
        min_index = start + M
        max_index = start + N
        def f(k):
            if k<min_index or k>max_index:
                return self.K0
            return list[k-start]

        return self.ps(f,min_index,**kwargs)
        
    def byTaylor(self,expr,v,at=0,**kwargs):
        assert not v == None
        assert isinstance(v,SymbolicVariable)

        def f(n):
            #too slow
            #if not at == 0 and n==0:
            #    return expr({v:at})-at
            #return simplify(diff(expr,v,n).substitute({v:at})/factorial(n))
            return self.K(expr.taylor(v,at,n).substitute({v:v+at}).coeff(v,n))

        #coeffs always returns non-empty list, at least [0,0] is contained
        min_index = expr.taylor(v,at,2).substitute({v:v+at}).coeffs(v)[0][1]
        return self.ps(f,min_index,**kwargs)

    def byConst(self,c,**kwargs):
        def f(n):
            if n == 0:
                return self.K(c)
            return self.K0
        return self.ps(f,0,**kwargs)
        
    def zero_element(self):
        return self.Zero

    def one_element(self):
        return self.One
        
    def __call__(self,p=None,v=None,at=None,**kwargs):
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

        if isinstance(p,Integer) or isinstance(p,int) or isinstance(p,Rational):
            return self.byConst(p,**kwargs)

        if isinstance(p,list):
            return self.byList(p,**kwargs)

        if isinstance(p,SymbolicExpression):
            if at == None:
                at = 0
            return self.byTaylor(p,v,at,**kwargs)

        if type(p) is type(lambda n: 0):
            if at == None:
                at = 0
            return self.byLambda(p,at,**kwargs)

        return self.byUndefined()

    def __init__(self,base_ring):
        if base_ring == None:
            return

        self.K = base_ring

        def PSF(f):
            return self.byLambda(f,T=PowerSeriesI)
        def PSF0N(f):
            return self.byLambda(f,T=PS0N)
        def PSF01(f):
            return self.byLambda(f,1,T=PS01)
        def PSS(seq):
            return self.byList(seq,T=PowerSeriesI)
        def PSS0N(seq):
            return self.byList(seq,T=PS0N)
        def PSS01(seq):
            return self.byList(seq,1,T=PS01)

        if self.K == int:
            self.K = Integer

        K = self.K
        K1 = K.one_element()
        self.K1 = K1
        K0 = K.zero_element()
        self.K0 = K0

        self.Zero = PSS([])
        self.One = PSS([K1])
        self.Id = PSS01([K1])
        self.Inc = PSS([K1,K1])
        self.Dec = PSS([K(-1),K1])
        self.Exp = PSF(lambda n: K(1/factorial(n)))
        self.Dec_exp = PSF01(lambda n: K0 if n==0 else K(1/factorial(n)))
        self.Log_inc = PSF01(lambda n: K0 if n==0 else K((-1)**(n+1)/Integer(n)))
        self.Sin = PSF01(lambda n: K0 if n % 2 == 0 else K((-1)**((n-1)/2)/factorial(n)))
        self.Cos = PSF(lambda n: K0 if n % 2 == 1 else K((-1)**(n/2)/factorial(n)))

        def arcsin(n):
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
        self.Arctan = PSF01(lambda n: K0 if n % 2== 0 else K((-1)**(n/2)/Integer(n)))

        self.Sinh = PSF01(lambda n: K0 if n % 2 == 0 else K(1/factorial(n)))
        self.Cosh = PSF(lambda n: K0 if n % 2 == 1 else K(1/factorial(n)))
        def arcsinh(n):
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
        self.Arctanh = PSF01(lambda n: K0 if n % 2 == 0 else K(1/Integer(n)))

        self.Bernoulli = (self.Id / self.Exp.dec()).derivatives()

        def tan(N):
            if N % 2 == 0:
                return K0
            n = (N + 1) / 2
            return K(self.Bernoulli[2*n] * (-4)**n * (1-4**n) / factorial(2*n))
        self.Tan = PSF01(tan)

        def tanh(N):
            if N % 2 == 0:
                return K0
            n = (N+1)/2
            return K(self.Bernoulli[2*n] * (-1)**(2*n) * 4**n * (4**n-1) / factorial(2*n))
        self.Tanh = PSF01(tanh)

        self.Xexp = PSF01(lambda n: K0 if n==0 else K(1/factorial(n-1)))
        """ x*exp(x) """

        self.Lambert_w = PSF01(lambda n: K0 if n==0 else K((-n)**(n-1)/factorial(n)))
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
        self.Sqrt_inc = PSF(sqrt_inc)

        #dont go into a recursion defining stirling1
        if isinstance(K,PowerSeriesRingI):
            return

        self.Stirling1 = PowerSeriesI(parent=self)
        def f(n):
            """
            Returns the sequence of Stirling numbers of the first kind.
            These are the coefficients of the polynomial x(x-1)(x-2)...(x-n+1).
            stirling1[n][k] is the coefficient of x^k in the above polynomial.
            """
            
            if n==0:
                res = self.byLambda(lambda k: 1 if k==0 else 0)
            else:
                g = self.Stirling1[n-1]
                res = self.byLambda(lambda k: g[k-1]-(n-1)*g[k],1)
        
            return res
        self.Stirling1.f = f

        def lehmer_comtet(n,k): #A008296
            return sum([binomial(l, k)*k^(l-k)*self.Stirling1[n][l] for l in range(k,n+1)],K0)
        self.Lehmer_comtet = PSF(lambda n: sum([k**(n-k)*binomial(n,k) for k in range(n+1)],K0))
        self.A000248  = self.Lehmer_comtet

        #self.selfpower_inc = PSF(lambda n: K(sum([ lehmer_comtet(n,k) for k in range(0,n+1))/factorial(n),K0))
        self.Selfpower_inc = PSF(lambda n: K(sum([ self.Stirling1[n][k]*self.A000248[k] for k in range(n+1)],K0)/factorial(n)))
        """
        Power series of x^x at 1
        """
        self.Superroot_inc = PSF(lambda n: K(sum([ self.Stirling1[n][k]*Integer(1-k)**(k-1) for k in range(n+1)],K0)/factorial(n)))
        """
        Powerseries of the inverse of x^x developed at 1.
        """

        def A003725(n):
            """
            Derivatives of exp(x*e^(-x)) at 0
            """
            return K(sum([ (-k)**(n-k)*binomial(n, k) for k in range(n+1)],K0))
        self.A003725 = PSF(A003725)

        self.Selfroot_inc = PSF(lambda n: K(sum([ self.Stirling1[n][k]*self.A003725[k] for k in range(n+1)],K0)/factorial(n)))
        """
        Development of x^(1/x) at 1
        """

        self.Inv_selfroot_inc = PSF(lambda n: K(sum([self.Stirling1[n][k]*K((k+1))**(k-1) for k in range(n+1)],K0)/factorial(n)))
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

        sage: P.Log_inc | P.Exp.dec().asPS0()
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Arcsin | P.Sin      
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Arctan | P.Tan
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Arctanh | P.Tanh
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Lambert_w | P.Xexp
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Selfpower_inc | P.Superroot_inc.dec().asPS0()
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: P.Selfroot_inc | P.Inv_selfroot_inc.dec().asPS0()          
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
        sage: (p << 1).log().smul(a[0]) + (a[1] | p) - a[1]
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: a = var('a')
        sage: p = PowerSeriesRingI(PolynomialRing(QQ,a))(exp(a*x)-1,x,T=PS0p)
        sage: pah = p.abel()
        sage: pac = p.abel2()
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
        sage: expps = PQ.Exp
        sage: expps.poly(10,x)
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
        sage: dexp = (expps - one).asPS01()
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
        sage: dbsrt = bsrt.ps0p()
        
        sage: #and now starting hyperbolic iteration                                          
        sage: dbsrt2 = dbsrt.it(x).it(1/x)
        sage: #Sage is not able to simplify                                                   
        sage: simplify(dbsrt2[3])
        (log(2)^3*(log(2)^(x + 2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)*2^x) - log(2)^3*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(8*(log(2)^2/4 - log(2)/2)) - log(2)^(x + 3)*2^(-x - 4)/3 + log(2)^(3*x + 3)*2^(-3*x - 4)/3)/(8*(log(2)^3/8 - log(2)/2)) - log(2)*(log(2)^(x + 2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)*2^x) - log(2)^3*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(8*(log(2)^2/4 - log(2)/2)) - log(2)^(x + 3)*2^(-x - 4)/3 + log(2)^(3*x + 3)*2^(-3*x - 4)/3)/(2*(log(2)^3/8 - log(2)/2)) - 2*log(2)^x*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))*(log(2)^2*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)) - log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(2*(log(2)^2/4 - log(2)/2)))/((log(2)^2/4 - log(2)/2)*2^x*(log(2)^(2*x)/2^(2*x) - log(2)^x/2^x)) + log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))*(log(2)^2*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(4*(log(2)^2/4 - log(2)/2)) - log(2)*(log(2)^(2*x + 2)*2^(-2*x - 3) - log(2)^(x + 2)*2^(-x - 3))/(2*(log(2)^2/4 - log(2)/2)))/((log(2)^2/4 - log(2)/2)*(log(2)^(2*x)/2^(2*x) - log(2)^x/2^x)))/(log(2)^(3*x)/2^(3*x) - log(2)^x/2^x)
        sage: #but numerically we can verify equality                                         
        sage: RR(dbsrt2[3](x=0.73)-dbsrt[3])
        -8.67361737988404e-19
    """

    def __init__(self,f=None,min_index=0,base_ring=None,parent=None):
        self._parent = parent
        if parent == None:
            if base_ring==None:
                self._parent = PowerSeriesRingI(QQ)
            else:
                self._parent = PowerSeriesRingI(base_ring)

        self.min_index = min_index #the minimal non-zero index
        self._memo = {}
        self._powMemo = {}
        self._itMemo = {}

        self.K = self._parent.K
        self.f = f

    def parent():
        return _parent

    def new(self,f=None,min_index=0,**kwargs):
        return type(self)(f,parent=self._parent,**kwargs)
        
    def base_ring(self):
        return self._parent.K

    def defrec(self,p):
        """
        Defines the power series self by another powerseries p 
        which is allowed to refer to self.
        """
        self.f = p.f
        
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
        return a.new(lambda n: value if n == index else a[n],a.min_index)

    def set_slice(a, i, j, seq):
        """
        Returns the powerseries that has a[i:j] replaced by seq.
        """
        return a.new(lambda n: seq[n-i] if i<=n and n<j else a[n],a.min_index)

    def derivatives(a):
        """
        The sequence of derivatives a[n]*n! of the powerseries a
        """
        return a.new(lambda n: a[n]*a.K(factorial(n)))

    def underivatives(a):
        """
        Returns the sequence a[n]/n!.
        """
        return a.new(lambda n: a[n]/a.K(factorial(n)))

    def inc(a):
        """
        Increment: a + 1
        """
        return a.new(lambda n: a[0]+a.K(1) if n==0 else a[n])

    def dec(a):
        """
        Decrement: a-1
        """
        return a.new(lambda n: a[0]-a.K(1) if n==0 else a[n])

    def smul(a,s):
        """
        Scalar multiplication with scalar s
        """
        return a.new(lambda n: a[n]*s,a.min_index)

    def __add__(a,b): # +
        """
        Addition:
        """
        def f(n):
            if n < a.min_index:
                if n < b.min_index:
                    return 0
                return b[n]
            if n < b.min_index:
                return a[n]
            return a[n]+b[n]
        return a.new(f,min(a.min_index,b.min_index))

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
            if n < a.min_index:
                if n < b.min_index:
                    return 0
                #a[0]==0
                return b[n]
            if n < b.min_index:
                #b[0]==0
                return a[n]
            return a[n]-b[n]
        return a.new(f,min(a.min_index,b.min_index))

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

        def ab(m,n):
            if a[m] == a.K(0):
                return a.K(0)
            return a[m]*b[n]

        def f(n):
            return sum([ab(k,n-k) for k in range(a.min_index,n+1-b.min_index)],a.K(0))
        return a.new(f,a.min_index+b.min_index)

    def times(a,b):
        """
        a.times(b) == a*b
        """
        return a*b

    def __div__(c,b): # /
        """
        Division: a/b*b=a, a*b/b=a
        """
        a = c.new()
        b.min_index = b.val()
        a.min_index = c.min_index - b.min_index

        def ab(m,n):
            if b[n] == b.K(0):
                return b.K(0)
            return a[m]*b[n]

        def f(n):
            if n<a.min_index:
                return 0
            return (c[n+b.min_index] - sum([ab(k,n+b.min_index-k) for k in range(a.min_index,n)],c.K(0)))/b[b.min_index]
        a.f = f
        return a

    def rcp(a):
        return a._parent.One/a

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
                res = a._parent.One
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
            return P.Exp | ( a.log() * t )
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
        return a.new(f)
        
    def sqrt(a):
        """
        Square root of a.
        """
        return a.pow_ni(1/2)

    def rt(a,n):
        """
        n-th root of a.
        """
        return a.pow_ni(1/n)

    def log(a):
        """
        Logarithm of powerseries a with a[0]==1.
        """

        P = a._parent
        if decidable0(a.K):
            assert a[0] == 1

        dec_a = a.ps0()

        return P.Log_inc | dec_a
    
    def __xor__(a,t): # ^
        #Not recognized as it seems to be mapped to ** in sage
        return NotImplemented

    def bell(a,n,k):
        """
        Returns the Bell polynomial of the sequence of variables a.
        """
        return derivatives(underivatives(a)**k).smul(1/factorial(k))
        

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
        r = abs(a[N])**(-1/Integer(N))
        l = r/sqrt(2.0)
        f = a.poly(N)
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

    def __or__(a,b): # |
        """
        p|q is the same as p.o(b)
        """
        return a.o(b)

    def o(a,b):
        """
        Composition: a.o(b).poly(m*n,x) == a.poly(m,b.poly(n,x)) 
        b must be of type PS0
        """
        assert isinstance(b,PS0)
#        if decidable0(b.K) and b[0] != 0:
#            raise ValueError, "0th coefficient of b must be 0 but is " + repr(b[0])
        def f(n):
            res = sum([a[k]*(b.npow(k)[n]) for k in range(n+1)],a.K(0))
            if a.min_index < 0:
                bi = b.rcp()
                res += sum([a[k]*(bi.npow(-k)[n]) for k in range(a.min_index,0)],a.K(0))
            return res
        return a.new(f,a.min_index*b.min_index)

    def ps0(a):
        """
        Returns a, with a[0]=0
        """
        return PS0(lambda n: a.K(0) if n == 0 else a[n], parent=a._parent)

    def ps0p(a):
        return PS0p(lambda n: a.K(0) if n == 0 else a[n], parent=a._parent)

    def isPS0(a):
        return a[0] == 0

    def isPS01(a):
        return a[0] == 0 and a[1] == 1

    def asPS0(a):
        """
        Returns it as PS0 without any questioning.
        """
        return PS0(a.f,parent=a._parent)

    def asPS01(a):
        """
        Returns it as PS01 without any questioning.
        """
        return PS01(a.f,parent=a._parent)
        

    def val(a):
        """
        Returns the first index i such that a[i] != 0
        Does not terminate if a == 0
        """
        n = a.min_index
        while a[n] == 0:
            n += 1
        return n

    def __lshift__(a,m=1):
        return a.new(lambda n: a[n+m])

    def __rshift__(a,m=1):
        return a.new(lambda n: 0 if n<m else a[n-m])

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

        return a.new(f,deg(a.min_index,m))

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
        """

        def f(n):
            if a[-1] != 0:
                raise ValueError, "Coefficient -1 must be 0, but it is: " + repr(a[-1])
            if n == 0:
                return c
            return a[n-1]/Integer(n)
            
        return a.new(f)

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

class PS0(PowerSeriesI):
    def apply(a,b):
        """
        a.apply(b) is the same as b | a
        """
        return b.o(a)

    def nit(a,n):
        """
        n times iteration (n times composition), n is a natural number
        """
        # assert n natural number
        if not a._itMemo.has_key(n):
            res = a._parent.Id
            for k in range(n):
                res = res.o(a)
            a._itMemo[n] = res
        return a._itMemo[n]

    def __and__(a,t): # &
        """
        p&t is the same as p.it(t)
        """
        
        return a.it(t)

    def __invert__(a):
        return a.inv()

    def inv(a):
        """
        Inverse: a.inv().o(f)=Id
        also ~a
        """
        if decidable0(a.K) and a[0] != 0:
            raise ValueError, "0th coefficient of a must be 0 but is " + repr(a[0])
        return a.it(-1)


    def julia(a):
        """
        diff(it(a,t),t)(t=0) = ln(a[1])*julia(a)
        """
        if decidable0(a.K):
            assert a[0] == 0
            assert a[1] != 0
        
        Poly=PolynomialRing(a.K,'x')
        b = PowerSeriesRingI(Poly)()
        b.min_index = 1

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

        return a.new(lambda n: h(b[n]),1)
        
    def itlog(a):
        """
        Iterative logarithm:
        itlog(f^t) == t*itlog(f)
        defined by: diff(f.it(t),t)(t=0)
        can be used to define the regular Abel function abel(f) by
        abel(f)' = 1/itlog(f)

        Refs:
        Eri Jabotinsky, Analytic iteration (1963), p 464
        Jean Ecalle, Theorie des Invariants Holomorphes (1974), p 19
        """

        #TODO this should be possible directly
        _t = var('_t')
        g = a.it(_t)
        def f(n):
           return diff(g[n],_t)(_t=0)
        res = a.new(f)
        res.min_index = res.val()
        return res



class PS0p(PS0):
    """
    PowerSeries p of the form p[0]=0 and p[1]!=0,1
    """
    def it(a,t):
        """
        Regular iteration at fixed point 0 for f'(0)!=1 (non-parabolic).
        """
        if decidable0(a.K):
            assert a[0]==0 and a[1]!=1

        b = a.new()
        b.min_index = 1
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

    def schroeder(a):
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
        s = a.new()
        s.min_index = 1
        def f(n):
            if n == 0:
                return 0
            if n == 1:
                return 1
            return sum([s[m]*a.npow(m)[n] for m in range(1,n)],a.K(0))/(q - q**n)
        s.f = f
        return s
        
    def abel(f):
        """
        The regular Abel function of a non-parabolic powerseries f has the form
        a(x)=(ln(x)+ps(x))/ln(q)
        where q=f[1]!=0,1 and ps is a powerseries
        
        This method returns ps
        """
        P = f._parent
        return P.Log_inc | ((f.schroeder()<<1) - P.One)

    def abel2(a):
        return a.new(a.julia().rcp().f,0).integral()
        

class PS01(PS0):
    """
    PowerSeries p of the form p[0]=0 and p[1]=1
    """

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

    def it0(p,t):
        N=p.valit()
        P = p._parent
        q = P()
        def f(n):
            if n < N:
                return P.Id[n]
            if n == N:
                return t * p[N]
            if n > N:
                r=p[n]
                r+=sum([p[m]*(q**m)[n] - q[m]*(p**m)[n] for m in range(N,n)])
                return r
            
        q.f = f
        return q

    def it(a,t):
        """
        Parabolic t-times iteration, i.e. for the case a[0]==0 and a[1]==1
        """

            
        def f(n):
            if decidable0(a.K):
                assert a[0] == 0, "The index of the lowest non-zero coefficient must be 1, but is " + repr(a.min_index)
                assert a[1] == 1, "The first coefficient must be 1, but is " + repr(a[1])

            if n == 1: return 1
            def c(m):
                return (-1)**(n-1-m)*binomial(t,m)*binomial(t-1-m,n-1-m)
            res = sum([c(m)*a.nit(m)[n] for m in range(n)],a.K(0))
            return res
        return a.new(f,1)

    def it(a,t):

        def f(n):
            if decidable0(a.K):
                assert a[0] == 0
                assert a[1] == 1

            return sum([binomial(t,m)*sum([binomial(m,k)*(-1)**(m-k)*a.nit(k)[n] for k in range(m+1)],a.K(0)) for m in range(n)],a.K(0))
        return a.new(f,1)

    def julia(a):
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
        return [resit,juli.set_index(-1,0).integral()]

