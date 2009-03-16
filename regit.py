"""
Regular Iteration

Author: Henryk Trappmann
"""

from sage.rings.complex_field import ComplexField

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

        itf = x.n(iprec)
        itf0 = x0.n(iprec)
        itf01 = f(itf0)
	yp = itf0
        while True:
            itf = f(itf)
            itf0 = itf01
            itf01 = f(itf0)

            y = (itf-itf0)/(itf01-itf0)
            #yp = y + 2**(-prec)+1
            print "yp:",yp
            print "y: ",y
            if abs(y-yp) < 2**(-prec):
                break
            yp = y
            
        return x.parent()(y)
        
    return r
   
def reg_schroeder_at(f,x0,a=0):
    """
    Takes a real function f with f(a)==a and 0<|f'(a)|<1 and 
    an initial value x0!=a with f^n(x0) -> a. 
    Computes the regular Schroeder function s that is determined by s(x0)=1 
    """

    def r(x,iprec=None):
        prec = x.prec()
        if iprec == None:
            iprec = 3*prec #heuristic

        f = with_prec(f,iprec,x)

        itf=x.n(iprec)
        itf0=x0.n(iprec)
        yp = (a-x)/(a-x0)
#         if yp == 1:
#             return 1
#         if yp > 1:
#             signum = 1
#         else:
#             signum = -1

        while True:
            itf=f(itf)
            itf0=f(itf0)
            y=(a-itf)/(a-itf0)
            
            #print y.prec(),itf.prec(),itf,itf0,y
            d = yp - y
#             if d*signum < 0:
#                 raise ZeroDivisionError
#             if d*signum < 2**(-prec):
            if abs(d) < 2**(-prec):
                break
            yp=y
        return x.parent()(y)
        
    return r

def princ_schroeder_at0(f):
    def r(x,iprec=None):
        prec = x.prec()
        if iprec == None:
            iprec = 3*prec #heuristic

        f = with_prec(f,iprec,x)

        #compute f'(0)
        c=f(RealField(iprec)(2**(-(iprec/2))))*2**(iprec/2)

        itf=x.n(iprec)
        cn=1
        yp = x
#        dmin = 2**(iprec/2)
        while True:
            print itf
            print exp(itf-l+k)+1
            itf=f(itf)
            cn*=c
            y=itf/cn
            
            #print y.prec(),itf.prec(),cn.prec(),cn,y
            d = abs(yp - y)
            if d<2**(-prec):
                break
            yp=y
#             if d < dmin:
#                 dmin = d
#             else:
#                 print "Warning"
        return x.parent()(y)
    return r;

def fixed_point(f,x0,prec=53,iprec=None,T=ComplexField):
    #slightly increase precision
    if iprec == None:
        iprec = prec+4

    K = T(prec)
    Ki = T(iprec)

    x0 = Ki(x0)
    f = with_prec(f,iprec,x0)

    yp = x0
    while True:
        y=f(yp)
        if abs(yp-y) < 2**(-prec):
            return K(y)
        yp=y

def lower_fixed_point_exp_base(b):
    xp = b
    x = b**b
    err = 2**(-b.prec())
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
    func_prec = f(x0.n(prec)).prec()
    if func_prec < prec:
        raise TypeError, "function must be able to return at least the same precision (returned: " + repr(func_prec) + ") as the argument (given: " + repr(iprec) + ")."
    return f


def to_prec(K,prec):
    if K == complex:
        return ComplexField(prec)
    if K == float:
        return RealField(prec)
    return type(K)(prec)
    
def reg_schroeder(f,x0,prec=53,iprec=None,T=ComplexField):
    fpcache = {}

    if iprec == None:
        iprec = 3*prec #heuristic

    K = T(prec)
    Ki = T(iprec)

    x0 = Ki(x0)

    a = fixed_point(f,x0,prec=iprec)

    f = with_prec(f,iprec,x0)

    def r(x,out=None):
        itf=Ki(x)
        itf0=Ki(x0)
        yp = 1
        #dmin = 2**(iprec/2)
        while True:
            itf=f(itf)
            itf0=f(itf0)
            #print itf, itf0
            y=(a-itf)/(a-itf0)
            
            #print y.prec(),itf.prec(),cn.prec(),cn,y
            d = abs(yp - y)
            if d<2**(-prec):
                break
            yp=y
        if out == None:
            return K(y)
        else:
            return [a,K(y)]
    return r;

def princ_schroeder(f):
    fpcache = {}

    def r(x,iprec=None,out=None):
        prec = x.prec()
        if iprec == None:
            iprec = 3*prec #heuristic

        f = with_prec(f,iprec,x)

        if not fpcache.has_key(prec):
            fpcache[prec] = fixed_point(f,x,prec=iprec)
        a = fpcache[prec]
        #print a

        #compute f'(0), no cache needed should be fast
        c=(f(a+2**(-(iprec/2)))-a)*2**(iprec/2)
        #print c

        itf=x.n(iprec)
        cn=1
        yp = x
#        dmin = 2**(iprec/2)
        while True:
            itf=f(itf)
            #print itf
            cn*=c
            y=(a-itf)/cn
            
            #print y.prec(),itf.prec(),cn.prec(),cn,y
            d = abs(yp - y)
            if d<2**(-prec):
                break
            yp=y
#             if d < dmin:
#                 dmin = d
#             else:
#                 print "Warning"
        if out == None:
            return x.parent()(y)
        else:
            return [a,c,x.parent()(y)]
    return r;

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
