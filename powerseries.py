from sage.structure.sage_object import SageObject
from sage.rings.arith import factorial
from sage.rings.arith import binomial

class PowerSeriesI(SageObject):
    """
    Cached infinite power series

    EXAMPLES:
        sage: from hyperops.powerseries import PowerSeriesI
        sage: #Predefined PowerSeries                                                         
        sage: expps = PowerSeriesI().Exp()
        sage: expps.poly(10,x)
        x^9/362880 + x^8/40320 + x^7/5040 + x^6/720 + x^5/120 + x^4/24 + x^3/6 + x^2/2 + x + 1
        sage: expps
        [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880, 1/3628800, ...]
        sage: PowerSeriesI().Zero()
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PowerSeriesI().One()
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: PowerSeriesI().Identity()
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: #finite powerseries                                                             
        sage: p = PowerSeriesI([1,2,3,4])
        sage: p.poly(10,x)
        4*x^3 + 3*x^2 + 2*x + 1
        sage: p
        [1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: one = PowerSeriesI([1])
        sage: id = PowerSeriesI([0,1])

        sage: #power series are just functions that map the index to the coefficient          
        sage: expps(30)
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
        sage: p**(-1)/p*p*p
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: p**2
        [1, 4, 10, 20, 25, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]
        sage: #composition only works for coefficient 0 being 0 in the second operand         
        sage: dexp = expps - one
        sage: expps.compose(dexp)
        [1, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]

        sage: #we come into interesting regions ...                                           
        sage: dexp.compose(dexp)
        [0, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]
        sage: dexp.iterate(2)
        [0, 1, 1, 5/6, 5/8, 13/30, 203/720, 877/5040, 23/224, 1007/17280, ...]
        sage: dexp.iterate(-1)
        [0, 1, -1/2, 1/3, -1/4, 1/5, -1/6, 1/7, -1/8, 1/9, -1/10, 1/11, -1/12, ...]
        sage: dexp.iterate(-1).compose(dexp)
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: hdexp = dexp.iterate(1/2)
        sage: hdexp
        [0, 1, 1/4, 1/48, 0, 1/3840, -7/92160, 1/645120, 53/3440640, -281/30965760, ...]
        sage: #verifying that shoudl be Zero                                                  
        sage: hdexp.iterate(2) - dexp
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ...]

        sage: #symbolic (parabolic) iteration                                                 
        sage: dexp.iterate(x)
        [0, 1, x/2, 5*(x - 1)*x/12 - (x - 2)*x/6, ...]
        sage: q = dexp.iterate(1/x).iterate(x)
        sage: q(3)
        (5*(1/x - 1)/(6*x) - (1/x - 2)/(3*x) + 1/(2*x^2))*(x - 1)*x/2 - (5*(1/x - 1)/(12*x) - (1/x - 2)/(6*x))*(x - 2)*x
        sage: #simiplify and compare                                                          
        sage: expand(q(3))
        1/6
        sage: dexp(3)
        1/6

        sage: #you can initialize power series with arbitrary functions on natural numbers    
        sage: #for example the power series of sqrt(2)^x can be given as                      
        sage: bsrt = PowerSeriesI(lambda n: diff(sqrt(2)^x,x,n)(x=0)/factorial(n))

        sage: #making the first coefficient 0 to get the decremented exponential   
        sage: def coeff(n):
        sage:     if n == 0:
        sage:         return 0
        sage:     else:
        sage:         return bsrt(n)
      
        sage: dbsrt = PowerSeriesI(coeff)
        
        sage: #and now starting hyperbolic iteration                                          
        sage: dbsrt2 = dbsrt.iterate(x).iterate(1/x)
       
        sage: #Sage is not able to simplify                                                   
        sage: simplify(dbsrt2(3))
        ...

        sage: #but numerically we can verify equality                                         
        sage: RR(dbsrt2(3)(x=0.73)-dbsrt(3))
        -8.67361737988404e-19
    """

    def __init__(self,p=[]):
        self._memo = {}
        self._powMemo = {}
        self._natitMemo = {}
        if isinstance(p,list):
            def f(n):
                if n<len(p):
                    return p[n]
                else:
                    return 0
            self.f = f
        else:
            self.f = p


    def __call__(self,n):
        if not self._memo.has_key(n):
            self._memo[n] = self.f(n)
        return self._memo[n]
        
    def __add__(a,b):
        def ret(n):
            return a(n)+b(n)
        return PowerSeriesI(ret)

    def __sub__(a,b):
        def ret(n):
            return a(n)-b(n)
        return PowerSeriesI(ret)

    def __mul__(a,b):
        scalar = True
        try:
            c=a(0)*b
        except TypeError:
            scalar = False

        #multiplication by scalar
        if scalar: return PowerSeriesI(lambda n: a(n)*b)

        #multiplication of two powerseries
        #maybe necessary to avoid evaluation of a(n) or b(n)
        if a(0) == 0 and b(0) == 0:
            def ret(n):
                return sum(a(k)*b(n-k) for k in range(1,n))
        else:
            def ret(n):
                return sum(a(k)*b(n-k) for k in range(n+1))
        return PowerSeriesI(ret)

    def __div__(a,b):
        return a*b.reciprocal()

    def __pow__(a,n):
        #only for integer n 
        if not isinstance(n,Integer) and not isinstance(n,int):
            raise TypeError, type(n)
        if not a._powMemo.has_key(n):
            if n >= 0:
                res = PowerSeriesI([1])
                for k in range(n):
                    res = res * a
            else:
                res = a.reciprocal()**(-n)
            a._powMemo[n] = res
        return a._powMemo[n]
    
    def __xor__(a,t):
        print "^"

    def __and_(a,t):
        print "&"

    def __or__(a,t):
        print "|"

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
        for n in range(80):
            coeff = a(n)
            s = repr(a(n)) + ", "
            if len(res)+len(s) > 76: break
            else: res += s

        res += "...]";
        #res = repr([ a(m) for m in range(10)])
        return res

                    
    def reciprocal(a):
        if a(0) == 0:
            print "0th coefficient must be invertible"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        f = PowerSeriesI()
        def g(n):
            if n == 0:
                return 1/a(0)
            return -sum(f(m)*a(n-m) for m in range(n))
        f.f = g
        return f

    def compose(a,b):
        if b(0) != 0:
            print "0th coefficient of b must be 0"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        def ret(n):
            return sum(a(k)*((b**k)(n)) for k in range(n+1))
        return PowerSeriesI(ret)

    def inverse(a):
        if a(0) != 0:
            print "0th coefficient must be 0"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        return a.iterate(-1)

    def iterate(a,t):
        if a(0) != 0:
            print "0th coefficient must be 0"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        if a(1) == 1: return a.parit(t)
        else: return a.hypit(t)

    def hypit(a,t):
        if a(0) != 0:
            print "0th coefficient must be 0"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        if a(1) == 0:
            print "1st coefficient must be nonzero"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        f = PowerSeriesI()
        def g(n):
            #print "(" + repr(n)
            if n == 0:
                #print ")"
                return 0
            if n == 1:
                #print ")"
                return a(1)**t
            res = a(n)*(f(1)**n)-f(1)*a(n)
            res += sum(a(m)*(f**m)(n) - f(m)*(a**m)(n) for m in range(2,n))
            res /= a(1)**n - a(1)
            #print ")"
            return res
        f.f = g
        return f

    def parit(a,t):
        if a(0) != 0:
            print "0th coefficient must be 0"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
        if a(1) != 1:
            print "1st coefficient must be 1"
            #TODO which is the correct exception to raise?
            raise ZeroDivisionError
            
        def f(n):
            if n == 0: return 0
            if n == 1: return 1
            def c(m):
                return (-1)**(n-1-m)*binomial(t,m)*binomial(t-1-m,n-1-m)
            res = sum(c(m)*a.natit(m)(n) for m in range(n))
            return res
        return PowerSeriesI(f)
        
    def natit(a,n):
        # assert n natural number
        if not a._natitMemo.has_key(n):
            res = a.Identity()
            for k in range(n):
                res = res.compose(a)
            a._natitMemo[n] = res
        return a._natitMemo[n]

    def poly(a,n,x='init'):
        if x == 'init':
            return lambda x: sum(a(k)*x**k for k in range(n))
        else:
            return sum(a(k)*x**k for k in range(n))
    
    def diff(a,m=1): return a.derivative(a,m)

    def derivative(a,m=1):
        return PowerSeriesI(lambda n: a(n+m)*prod(k for k in range(n+1,n+m+1)))

    def integral(a,m=1):
        def f(n):
            if n < m:
               return 0
            return a(n-m)/prod(k for k in range(n-m+1,n+1))
        return PowerSeriesI(f)

    #static methods
    def Exp(self):
        return PowerSeriesI(lambda n: 1/factorial(n))

    def DecExp(self):
        def f(n):
            if n == 0: return 0
            else: return 1/factorial(n)
        return PowerSeriesI(f)

    def Identity(self):
        return PowerSeriesI([0,1])
    
    def One(self):
        return PowerSeriesI([1])

    def Zero(self):
        return PowerSeriesI([])
