"""
Regular Iteration

Author: Henryk Trappmann
"""

from sage.rings.complex_field import ComplexField
from sage.misc.functional import n

def par_abel(f,x0):
    """
    Takes a function f with f'(a)=1 and f^(m)(a)<0 for
    the first m>1 with f^(m)!= 0
    Computes the regular Abel function with alpha(x0)=0. 
    """
    
    def r(x,iprec=None):
        """
        Principal Abel function.
        The precision of x is taken as the precision of the outcome.
        """
        prec = x.prec()
        if iprec == None:
            iprec = 5*prec #heuristic

        itf = n(x,iprec)
        itf0 = n(x0,iprec)
        itf01 = f(itf0)
	yp = itf0
        while True:
            itf = f(itf)
            itf0 = itf01
            itf01 = f(itf0)

            y = (itf-itf0)/(itf01-itf0)
            print "yp:",yp
            print "y: ",y
            if abs(y-yp) < 2**(-prec):
                break
            yp = y
            
        return x.parent()(y)
        
    return r
   
def reg_schroeder(f,x0,prec=None,iprec=None,T=ComplexField):
    """
    Takes a (real or complex) function f with f(a)==a and 0<|f'(a)|<1 and 
    an initial value x0!=a with f^n(x0) -> a. 
    Computes the regular Schroeder function s that is determined by s(x0)=1.
    The Schr\"oder function of f is the same as that of f^{-1} so you always
    can choose 0<|f'(a)|<1.
    """

    if prec == None:
        prec = x0.prec()

    if iprec == None:
        iprec = 3*prec #heuristic
    
    K = T(iprec)
    err = K(2)**(-prec)

    x0 = K(x0)

    f = with_prec(f,iprec,x0)
    a = fixed_point(f,x0,prec=iprec)


    def r(x):
        itf=K(x)
        #itf=n(T(x),iprec)
        itf0=K(x0)
        #itf0=n(x0,iprec)
        yp = (a-itf)/(a-itf0)

        while True:
            itf=f(itf)
            itf0=f(itf0)
            y=(a-itf)/(a-itf0)
            
            #print y.prec(),itf.prec(),itf,itf0,y
            d = yp - y
            if abs(d) < err:
                break
            yp=y
        return n(y,prec)
    return r


def princ_schroeder(f,x0,prec=None,iprec=None,T=ComplexField,out=None):
    """
    Takes a (real or complex) function f with f(a)==a and 0<|f'(a)|<1 and 
    an x0 such that f^n(x0)->a.
    Computes the regular Schroeder function s that is determined by s(a)=1.
    The Schr\"oder function of f is the same as that of f^{-1} so you always
    can choose 0<|f'(a)|<1.

    If out!=None then [a,f'(a),s] is returned.
    """

    if prec == None:
        prec = x0.prec()

    if iprec == None:
        iprec = 3*prec #heuristic
    
    K = T(iprec)
    x0 = K(x0)

    f = with_prec(f,iprec,x0)
    a = fixed_point(f,x0,prec=iprec)

    #compute f'(a), no cache needed should be fast
    d = K(2)**(-int(iprec)/2)
    c=(f(a+d)-a)/d

    err = K(2)**(-prec)

    def r(x):
#        print x,
        itf=K(x)
        cn=1
        yp = a-itf

        while True:
#            print yp
            itf=f(itf)
            cn*=c
            y=(a-itf)/cn
            
            d = abs(yp - y)
            if d<err:
                break
            yp=y
        return T(prec)(y)

    if out == None:
        return r
    else:
        return [a,c,r]

    return r;

def compose(f,g):
    return lambda x: f(g(x))

def nit(f,n):
    if n==0:
        return lambda x: x
    if n==1:
        return lambda x: f(x)
    m1 = int(n)/2
    m2 = n - m1
    return compose(nit(f,m1),nit(f,m2))
    
def newton_it(f,prec=53,iprec=None,T=ComplexField):

    if iprec == None:
        iprec = prec + 4

    K = T(iprec)

    err = K(2)**(-prec)

    def r(t,x):
        fit = {}
        y = K(0)
        fit[0] = K(x)
        n = 1
        
        while True:
            fit[n] = f(fit[n-1])
            print 'n',n,'fit[n]',fit[n]
            s = sum([binomial(n,k) * Integer(-1)**(n-k) *fit[k] for k in range(n+1)])
            print 's',s
            d = binomial(t,n)*s
            y += d
            print y
            if abs(d)<err:
                return T(prec)(y)
            n+=1

    return r
    
def fixed_point(f,x0,prec=53,iprec=None,T=ComplexField):
    #slightly increase precision

    if iprec == None:
        iprec = prec+4

    K = T(iprec)

    err = K(2)**(-prec)

    x0 = K(x0)
    f = with_prec(f,iprec,x0)

    yp = x0

    while True:
        y=f(yp)
        if abs(yp-y) < err:
            return T(prec)(y)
        yp=y

def lower_fixed_point_exp_base(b,prec=None,iprec=None):
    T = RealField

    if prec == None:
        prec = b.prec()
    if iprec == None:
        iprec = prec + 4
        
    K = T(iprec)
    err = K(2)**(-prec)

    xp = K(b)
    x = xp**xp
    while x > (err+xp)*b**(-err):
        xp = x
        x = b**xp
        #print err, xp, x, (err+xp)*b**(-err)
    return x
        
def with_prec(f,prec,x0):
    for name in f.func_code.co_varnames:
        if name == 'prec':
            def res(*args,**kwargs):
                kwargs['prec']=prec
                return f(*args,**kwargs)
            return res
    func_prec = f(n(x0,prec)).prec()
    if func_prec < prec:
        raise TypeError, "function must be able to return at least the same precision (returned: " + repr(func_prec) + ") as the argument (given: " + repr(iprec) + ")."
    return f


def to_prec(K,prec):
    if K == complex:
        return ComplexField(prec)
    if K == float:
        return RealField(prec)
    return type(K)(prec)
    
def ellipt_abel(f):
    s=princ_schroeder(f)
    def r(x):
        [a,c,y]=s(x,out=1)
        return log(y,c)
    return r

def rslog1(b):
    """
    An implementation of the regular super log which uses the
    principial Schroeder function.

    b can be an expression that is evaluated with type of x.
    The precision of the outcome is determined by the precision of x.
    For example:

    rslog1(log(2))(RealField(100)(0.5))
    """
    f=lambda x: x.parent()(b)**x
    s=princ_schroeder(f)
    s1cache = {}
    def r(x,iprec=None):
        prec = x.prec()
        if iprec == None:
            iprec = prec+4
        
        if not s1cache.has_key(prec):
            s1cache[prec]=s(1,prec=iprec)
        s1=s1cache[prec]

        [a,c,y]=s(x,prec=iprec,out=1)
        return log(y/s1,c)
    return r

def rslog2(b):
    """
    An implementation of the regular super log which uses a
    suitable regular Schroeder function.

    b can be an expression that is evaluated with type of x .
    It has to satisfy -e < ln(b) < 1/e.
    The precision of the outcome is determined by the precision of x.
    For example:

    rslog2(log(2))(RealField(100)(0.5))
    """
    f=lambda x: x.parent()(b)**x
    s=reg_schroeder(f)
    def r(x,iprec=None):
        prec = x.prec()
        if iprec == None:
            iprec = prec + 4

        [a,y]=s(x,1,prec=iprec,out=1)
        return x.parent()(log(y,log(a)))
    return r

def rslog_at(b,k):
    """
    the regular super logarithm developed at the by index k 
    specified fixed point.
    """

def _it(f,t,x,d,N):
    it_memo = {}
    pow_memo = {}

    def fbdn(n):
        if not it_memo.has_key(n):
            if n==0:
                it_memo[n] = x
                pow_memo[n] = 1
            else:
                it_memo[n] = f(it_memo[n-1])
                pow_memo[n] = d*pow_memo[n-1]
        return it_memo[n]/pow_memo[n]

    return d**t*sum([binomial(t,n)*sum([binomial(n,k)*(-1)**(n-k)*fbdn(k) for k in range(0,n+1)]) for n in range(0,N+1)])
        
    
def it(f,t,x,N):
    it_memo = {}

    def nit(n):
        if not it_memo.has_key(n):
            if n==0:
                it_memo[n] = x
            else:
                it_memo[n] = f(it_memo[n-1])
                print it_memo[n]
        return it_memo[n]

    return sum([binomial(t,n)*sum([binomial(n,k)*(-1)**(n-k)*nit(k) for k in range(0,n+1)]) for n in range(0,N+1)])

def _tests():
    w=princ_schroeder_at0(lambda x: 2*(sqrt(RR(2.0))**x-1));
    
    try:
        w(RR(1.0))
    except ZeroDivisionError:
        print "passed"

    w=princ_schroeder_at0(lambda x: 2*(sqrt(x.parent()(2.0))**x-1));
    print w(RealField(100)(1))

    f=lambda x: sqrt(x.parent()(2.0))**x
    print fixed_point(f,RR(0))
    s=princ_schroeder(f)
    a=ellipt_abel(f)
    print s(RR(0))
    print s(RR(1))
    print a(RR(0))
    print a(RR(1))
