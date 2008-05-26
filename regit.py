"""
Author: Henryk Trappmann
"""

def princ_abel(f):
    """
    Takes a function f with f'(a)=1 and f^(m)(a)<0 for
    the first m>1 with f^(m)!= 0
    Computes the principal Abel function. 
    """
    
    def r(x,iprec='_default'):
        """
        Principal Abel function.
        The precision of x is taken as the precision of the outcome.
        """
        prec = x.prec()
        if iprec == '_default':
            iprec = 3*prec #heuristic
        R=type(x.parent())(iprec)

        itf = x
        itf0 = (x + f(x))/2
        itf01 = f(itf0)
        while True:
            itf = f(itf)
            itf0 = itf01
            itf01 = f(itf0)

            y = (itf-itf0)/(itf01-itf0)
            if abs(y-yp) < 2**(-prec):
                break
            yp = y
            
        return x.parent()(y)
        
    return r
    
def reg_schroeder_at(f,x0,a=0):
    """
    Takes a function f with f(0)==0 and 0<|f'(0)|<1 and an initial value x0!=a.
    Computes the regular Schroeder function s that is determined by s(x0)=1
    """

    def r(x,iprec='_default'):
        prec = x.prec()
        if iprec == '_default':
            iprec = 3*prec #heuristic
        R=type(x.parent())(iprec)

        _check_funcprec(f,x,R)

        itf=R(x)
        itf0=R(x0)
        yp = (a-x)/(a-x0)
        if yp == 1:
            return 1
        if yp > 1:
            signum = 1
        else:
            signum = -1

        while True:
            itf=f(itf)
            itf0=f(itf0)
            y=(a-itf)/(a-itf0)
            
            #print y.prec(),itf.prec(),itf,itf0,y
            d = yp - y
            if d*signum < 0:
                raise ZeroDivisionError
            if d*signum < 2**(-prec):
                break
            yp=y
        return x.parent()(y)
        
    return r

def princ_schroeder_at0(f):
    def r(x,iprec='_default'):
        prec = x.prec()
        if iprec == '_default':
            iprec = 3*prec #heuristic
        R=type(x.parent())(iprec)

        _check_funcprec(f,x,R)

        #compute f'(0)
        c=f(R(2)**(-(iprec/2)))*2**(iprec/2)

        itf=R(x)
        cn=1
        yp = x
        dmin = 2**(iprec/2)
        while True:
            itf=f(itf)
            cn*=c
            y=itf/cn
            
            #print y.prec(),itf.prec(),cn.prec(),cn,y
            d = abs(yp - y)
            if d<2**(-prec):
                break
            yp=y
            if d < dmin:
                dmin = d
            else:
                print "Warning"
        return x.parent()(y)
    return r;

def _check_funcprec(f,x,R):
    iprec = R(x).prec()
    func_prec = f(R(x)).prec()
    if  func_prec < iprec:
        raise ZeroDivisionError, "function must be able to return at least the same precision (returned: " + repr(func_prec) + ") as the argument (given: " + repr(iprec) + ")."


def fixed_point(f,x0,iprec='_default'):
    #slightly increase precision
    prec = x0.prec()
    if iprec == '_default':
        iprec = prec+4
    R=type(x0.parent())(iprec)

    _check_funcprec(f,x0,R)

    yp = R(x0)
    while True:
        y=f(yp)
        if abs(yp-y) < 2**(-prec):
            return y
        yp=y

def reg_schroeder(f):
    fpcache = {}

    def r(x,x0,iprec='_default',out='_default'):
        prec = x.prec()
        if iprec == '_default':
            iprec = 3*prec #heuristic
        R=type(x.parent())(iprec)

        _check_funcprec(f,x,R)

        if not fpcache.has_key(prec):
            fpcache[prec] = fixed_point(f,R(x))
        a = fpcache[prec]
        #print a

        itf=R(x)
        itf0=R(x0)
        yp = (a-x)/(a-x0)
        dmin = 2**(iprec/2)
        while True:
            itf=f(itf)
            itf0=f(itf0)
            y=(a-itf)/(a-itf0)
            
            #print y.prec(),itf.prec(),cn.prec(),cn,y
            d = abs(yp - y)
            if d<2**(-prec):
                break
            yp=y
            if d < dmin:
                dmin = d
            else:
                print "Warning"
        if out == '_default':
            return x.parent()(y)
        else:
            return [a,x.parent()(y)]
    return r;

def princ_schroeder(f):
    fpcache = {}

    def r(x,iprec='_default',out='_default'):
        prec = x.prec()
        if iprec == '_default':
            iprec = 3*prec #heuristic
        R=type(x.parent())(iprec)

        _check_funcprec(f,x,R)

        if not fpcache.has_key(prec):
            fpcache[prec] = fixed_point(f,R(x))
        a = fpcache[prec]
        #print a

        #compute f'(0), no cache needed should be fast
        c=(f(a+R(2)**(-(iprec/2)))-a)*2**(iprec/2)
        #print c

        itf=R(x)
        cn=1
        yp = x
        dmin = 2**(iprec/2)
        while True:
            itf=f(itf)
            cn*=c
            y=(a-itf)/cn
            
            #print y.prec(),itf.prec(),cn.prec(),cn,y
            d = abs(yp - y)
            if d<2**(-prec):
                break
            yp=y
            if d < dmin:
                dmin = d
            else:
                print "Warning"
        if out == '_default':
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
    def r(x,iprec='_default'):
        prec = x.prec()
        if iprec == '_default':
            iprec = prec+4
        R=type(x.parent())(iprec)
        
        if not s1cache.has_key(prec):
            s1cache[prec]=s(R(1))
        s1=s1cache[prec]

        [a,c,y]=s(R(x),out=1)
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
    def r(x,iprec='_default'):
        prec = x.prec()
        if iprec == '_default':
            iprec = prec + 4
        R=type(x.parent())(iprec)

        [a,y]=s(R(x),1,out=1)
        return x.parent()(log(y,log(a)))
    return r

def rslog_at(b,k):
    """
    the regular super logarithm developed at the by index k 
    specified fixed point.
    """

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
