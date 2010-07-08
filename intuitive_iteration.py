from sage.functions.log import log, ln
from sage.functions.other import sqrt,real,imag,ceil,floor
from sage.functions.trig import tan
from sage.matrix.constructor import Matrix, identity_matrix
from sage.misc.functional import n as num
from sage.misc.persist import save
from sage.modules.free_module_element import vector
from sage.rings.arith import factorial, binomial
from sage.rings.complex_field import ComplexField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.integer import Integer
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ
from sage.rings.real_mpfr import RR, RealField
from sage.symbolic.constants import e
from sage.symbolic.ring import SR

from sage.hyperops.formal_powerseries import FormalPowerSeries

class IntuitiveAbel:
    def __init__(self,f,N,iprec=512,u=None,x0=0,fname=None):
        """
        x0 is the development point for the Carleman matrix for the abel function
        u is the initial value such that abel(u)=0 or equivalently super(0)=u

        if no u is specified we have abel(x0)=0
        iprec=None means try to work with the rational numbers
        """

        self.f = f
        self.N = N
        self.iprec = iprec
        x0sym = x0
        self.x0sym = x0sym

        self.prec = None

        x0name = repr(x0sym)
        if x0name.find('.') > -1:
            if x0.is_real():
                x0name = repr(float(x0sym)).strip('0').replace('.',',')
            else:
                x0name = repr(complex(x0sym)).strip('0').replace('.',',')
        # by some reason save does not work with additional . inside the path

        if iprec==None:
            iprec_part = 'QQ'
        else:
            iprec_part = '%05d'%iprec

        self.path = "savings/iabel_%s"%fname + "_N%04d"%N + "_iprec" + iprec_part + "_a%s"%x0name

        if iprec != None:
            x0 = num(x0sym,iprec)
            if x0.is_real():
                R = RealField(iprec)
            else:
                R = ComplexField(iprec)
        else:
            R = QQ

        self.x0 = x0
        self.R = R

	#Carleman matrix
        #too slow
        #C = Matrix([ [ln(b)**n/factorial(n)*sum([binomial(m,k)*k**n*(b**x0)**k*(-x0)**(m-k) for k in range(m+1)]) for n in range(N)] for m in range(N)])

        if isinstance(f,FormalPowerSeries):
            coeffs = [ f[n] for n in xrange(0,N) ]
        else:
            x = f.args()[0]
            coeffs = taylor(f.substitute({x:x+x0sym})-x0sym,x,0,N).polynomial(self.R)

        def psmul(A,B):
            return [sum([A[k]*B[n-k] for k in xrange(n+1)]) for n in xrange(N)]
        
        C = Matrix(R,N)

        row = vector(R,[1]+(N-1)*[0])
        C[0] = row
        for m in xrange(1,N):
            row = psmul(row,coeffs)
            C[m] = row
  
        A = (C - identity_matrix(N)).submatrix(1,0,N-1,N-1)
        self.A = A.transpose()

        print "A computed."

        if iprec != None:
            A = num(A,iprec)

        row = A.solve_left(vector([1] + (N-2)*[0]))

        print "A solved."

        self.abel0coeffs = [0]+[row[n] for n in range(N-1)]
        self.abel0poly = PolynomialRing(R,'x')(self.abel0coeffs[:int(N)/2])
        
        self.abel_raw0 = lambda z: self.abel0poly(z-self.x0)

        self.c = 0
        if not u == None:
            self.c = - self.abel(u)

    def abel(self,x):
        x = num(x,self.iprec)
	res = self.abel_raw0(x)
        if self.prec == None:
            return res
        return res.n(self.prec)

    __call__ = abel

    def calc_prec(self,debug=0):
        if self.prec != None:
            return self.prec
        iv0 = IntuitiveAbel(self.f,self.N-1,iprec=self.iprec,x0=self.x0sym)
        self.iv0 = iv0
        d = lambda x: self.abel(x) - iv0.abel(x)
        a = find_root(lambda x: (self.f(x)+x)/2-self.x0,self.x0-100,self.f(self.x0))
        maximum = find_maximum_on_interval(d,self.x0-a,self.x0+self.f(a),maxfun=20)
        minimum = find_minimum_on_interval(d,self.x0-a,self.x0+self.f(a),maxfun=20)
        if debug>=1: print "max:", maximum[0].n(20), 'at:', maximum[1]
        if debug>=1: print "min:", minimum[0].n(20), 'at:', minimum[1]
        self.err = max( abs(maximum[0]), abs(minimum[0]))
        print "err:", self.err.n(20)
        self.prec = floor(-self.err.log(2))
        
        return self

    def backup(self):
        print "Writing to `" + self.path + ".sobj'."
        save(self,self.path)
        if self.prec != None: save(self.prec,self.path+"_prec"+repr(self.prec))
        return self

class IntuitiveSuper(IntuitiveAbel):
    def __init__(self,f,N,iprec=512,u=None,x0=0,fname=None):
        ia = IntuitiveAbel(f,N,iprec=iprec,u=u,x0=x0,fname=fname)
    
        self.iprec = ia.iprec
        abel0ps = FormalPowerSeriesRing(R)(ia.abel0coeffs)
        super0ps = ia.abel0ps.inv()
        #print self.abel0ps | self.super0ps
        self.super0coeffs = super0ps[:N]
        self.super0poly = PolynomialRing(R,'x')(self.super0coeffs[:int(N)/2])

        print "abel powerseries reversed."


    def super_raw(self,x):
        x0 = self.x0
        c = self.c
        N = self.N
        a = self.super0coeffs

        return x0+sum([a[n]*(x-c)**n for n in range(1,int(N)/2)])

    def super(self,x):
        """
        Development point is x0-1
        """
        if isinstance(x,float) and self.iprec != None:
           x = RealField(self.iprec)(x)
            
        super = self.super
        super_raw = self.super_raw
        b = self.b
        c = self.c

        xt = x - c
        if real(xt)<-0.5:
            return log(super(x+1))/log(b)
        if real(xt)>0.5:
            return b**(super(x-1))
        return super_raw(x)

    def calc_prec():
        if self.prec != None:
            return self.prec
        iv0 = IntuitiveAbel(self.bsym,self.N-1,iprec=self.iprec,x0=self.x0sym)
        self.iv0 = iv0
        self.err = abs(iv0.sexp(0.5) - self.sexp(0.5))
        print "err:", self.err.n(20)
        self.prec = floor(-log(self.err)/log(2.0))
