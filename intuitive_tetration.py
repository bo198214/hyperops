from sage.symbolic.constants import e
from sage.functions.other import sqrt,real,imag,ceil,floor
from sage.functions.log import log, ln
from sage.functions.trig import tan
from sage.matrix.constructor import Matrix, identity_matrix
from sage.misc.persist import save
from sage.modules.free_module_element import vector
from sage.rings.arith import factorial
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.arith import binomial
from sage.rings.real_mpfr import RR, RealField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.integer import Integer
from sage.rings.rational_field import QQ
from sage.rings.complex_field import ComplexField
from sage.symbolic.ring import SR
import mpmath


class IntuitiveSlog:
    def __init__(self,b,N,iprec=None,x0=0):
        self.bsym = b
        self.N = N
        self.iprec = iprec
        self.x0sym = x0

        self.c = 0
        self.prec = None


        bname = repr(b).replace('.',',')
        if b == sqrt(2):
           bname = "sqrt2"
        if b == e**(1/e):
           bname = "eta"

        x0name = repr(x0)
        if x0name.find('.') > -1:
            if x0.is_real():
                x0name = repr(float(x0)).replace('.',',')
            else:
                x0name = repr(complex(x0)).replace('.',',')
        # by some reason save does not work with additional . inside the path

        self.path = "savings/islog_%s"%bname + "_N%04d"%N + "_iprec%05d"%iprec + "_a%s"%x0name

        if iprec != None:
            b = b.n(iprec)
            self.b = b
            x0 = x0.n(iprec)
            if x0.is_real():
                R = RealField(iprec)
            else:
                R = ComplexField(iprec)
            self.x0 = x0
        else:
            if b == e and x0 == 0:
                R = QQ
            else:
                R = SR
        self.R = R


	#Carleman matrix
        if x0 == 0:
            #C = Matrix([[ m**n*log(b)**n/factorial(n) for n in range(N)] for m in range(N)])
            coeffs = [ln(b)**n/factorial(n) for n in xrange(N)]
        else:
            #too slow
            #C = Matrix([ [ln(b)**n/factorial(n)*sum([binomial(m,k)*k**n*(b**x0)**k*(-x0)**(m-k) for k in range(m+1)]) for n in range(N)] for m in range(N)])

            coeffs = [b**x0-x0]+[b**x0*ln(b)**n/factorial(n) for n in xrange(1,N)]
        def psmul(A,B):
            N = len(B)
            return [sum([A[k]*B[n-k] for k in xrange(n+1)]) for n in xrange(N)]
        
        C = Matrix(R,N)

        row = vector(R,[1]+(N-1)*[0])
        C[0] = row
        for m in xrange(1,N):
            row = psmul(row,coeffs)
            C[m] = row
  
        A = (C - identity_matrix(N)).submatrix(1,0,N-1,N-1)

        print "A computed."

        if iprec != None:
            A = A.n(iprec)

        row = A.solve_left(vector([1] + (N-2)*[0]))[0]

        print "A solved."

        self.slog0coeffs = [0]+[row[n] for n in range(N-1)]
        
        slog0ps = FormalPowerSeriesRing(R)(self.slog0coeffs)
        sexp0ps = slog0ps.inv()
        #print self.slog0ps | self.sexp0ps
        self.sexp0coeffs = sexp0ps[:N]

        print "slog reversed."

        #the primary or the upper fixed point
	mpmath.mp.dps = ceil(iprec/ln(10.0)*ln(2.0))
        L = mpmath.lambertw(-mpmath.ln(b),-1)/(-mpmath.ln(b))
        L = ComplexField(iprec)(L.real,L.imag)
        self.L = L

        #lower fixed point
        bL = None
        if b <= R(e**(1/e)):
             bL = mpmath.lambertw(-mpmath.ln(b),0)/(-mpmath.ln(b))
             bL = RealField(iprec)(bL)
        self.bL = bL

        if bL == None or x0 < bL:
            #slog(0)==-1
	    self.c = -1 - self.slog(0.0)                   
        elif not bL == None and bL < x0 and x0 < L:
            #slog(e)==0
	    self.c = -self.slog(R(e))
	else:
            self.c = 0
       

    def slog_raw(self,z):
        """
        The raw slog without continuation.
        """
        x0 = self.x0
        a = self.slog0coeffs
        N = self.N
        c = self.c
        
        return c+sum([a[n]*(z-x0)**n for n in range(1,int(N)/2)])
        
    def cmp_ir(self,z):
        """ 
        returns -1 for left, 0 for in, and 1 for right from initial region
        cut line is on the north ray from L.
        """
        L = self.L
        x0 = self.x0
        if x0 > 0.5:
            if real(z) > real(L) and abs(z) < abs(L):
                return 0
            if real(z) < real(L):
                return -1
            if real(z) > real(L):
                return 1
        else:
            if imag(z) > imag(L):
                if real(z) > real(L):
                    return 1
                if real(z) < real(L):
                    return -1
            if real(z) < real(L) and real(z) > log(real(L)) + log(sqrt(1+tan(imag(z))**2)):
                return 0
            if real(z) > real(L):
                return 1
            if real(z) < real(L):
                return -1

    def slog2(self,z):
        """
        In the complex plane continued slog for base > eta
        """
        if isinstance(z,float) and self.iprec != None:
           z = RealField(self.iprec)(z)
        
        slog = self.slog2
        slog_raw = self.slog_raw
        b = self.b
        x0 = self.x0
        N = self.N

        if self.cmp_ir(z) == -1:
            return slog(b**z)-1
        if self.cmp_ir(z) == +1:
            return slog(log(z)/log(b))+1
        return slog_raw(z)

    def slog1(self,z):
        """
        In the complex plane continued slog for base <= eta
        """
        if isinstance(z,float) and self.iprec != None:
           z = RealField(self.iprec)(z)
        
        slog = self.slog1
        slog_raw = self.slog_raw
        b = self.b
        x0 = self.x0
        N = self.N

        r = abs(x0-self.L)

        if abs(z-x0) > r:
            return slog(b**z)-1
        return slog_raw(z)

    def slog(self,x):
        """
        Development point is x0
        real continued slog
        """
        if isinstance(x,float) and self.iprec != None:
           x = RealField(self.iprec)(x)

        slog = self.slog
        slog_raw = self.slog_raw
        b = self.b
        x0 = self.x0
        L = self.L
        bL = self.bL
        
        if bL == None or x0 < bL or x0 > L:
            sign = 1
        else:
            sign = -1

        if sign*(x - self.x0 + 0.5) < 0:
            return slog(b**x)-1
        if sign*(x - b**(x0 - 0.5)) > 0:
            return slog(log(x)/log(b))+1
        return slog_raw(x)

    def sexp_raw(self,x):
        x0 = self.x0
        c = self.c
        N = self.N
        a = self.sexp0coeffs

        return x0+sum([a[n]*(x-c)**n for n in range(1,int(N)/2)])

    def sexp(self,x):
        """
        Development point is x0-1
        """
        if isinstance(x,float) and self.iprec != None:
           x = RealField(self.iprec)(x)
            
        sexp = self.sexp
        sexp_raw = self.sexp_raw
        b = self.b
        c = self.c

        xt = x - c
        if real(xt)<-0.5:
            return log(sexp(x+1))/log(b)
        if real(xt)>0.5:
            return b**(sexp(x-1))
        return sexp_raw(x)

    def calc_prec(self):
        if self.prec != None:
            return self.prec
        iv0 = IntuitiveSlog(self.bsym,self.N-1,iprec=self.iprec,x0=self.x0sym)
        self.prec = floor(-log(abs(iv0.sexp(0.5) - self.sexp(0.5)))/log(2.0))
        print "sexp precision: " , self.prec
        return self

    def backup(self):
        print "Writing to `" + self.path + ".sobj'."
        save(self,self.path)
        if self.prec != None: save(self.prec,self.path+"_prec"+repr(self.prec))
        return self
