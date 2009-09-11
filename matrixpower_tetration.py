from sage.functions.log import log
from sage.functions.other import sqrt,real,imag,ceil
from sage.functions.trig import tan
from sage.matrix.constructor import Matrix, identity_matrix
#from sage.misc.functional import n
from sage.misc.persist import save
from sage.modules.free_module_element import vector
from sage.rings.arith import factorial
from sage.rings.formal_powerseries import FormalPowerSeriesRing, FormalPowerSeries0
from sage.rings.complex_field import ComplexField
from sage.rings.integer import Integer
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.real_mpfr import RR, RealField
from sage.symbolic.constants import e
from sage.symbolic.ring import SR

class MatrixPowerSexp:
    def __init__(self,b,N,iprec,x0=0):
        self.bsym = b
        self.N = N
        self.iprec = iprec
        self.x0sym = x0
        self.prec = None


        bname = repr(b).replace('.',',')
        if b == sqrt(2):
           bname = "sqrt2"
        if b == e**(1/e):
           bname = "eta"
           
        x0name = repr(x0)
        if x0name.find('.') > -1:
            if x0.is_real():
                x0name = repr(float(real(x0))).replace('.',',')
            else:
                x0name = repr(complex(x0)).replace('.',',')
        # by some reason save does not work with additional . inside the path

        self.path = "savings/msexp_%s"%bname + "_N%04d"%N + "_iprec%05d"%iprec + "_a%s"%x0name

        b = b.n(iprec)
        self.b = b
        x0 = x0.n(iprec)
        self.x0 = x0
        if isinstance(x0,sage.rings.real_mpfr.RealNumber):
            R = RealField(iprec)
	else:
            R = ComplexField(iprec)    

        #symbolic carleman matrix
        if x0 == 0:
            #C = Matrix([[ m**n*log(b)**n/factorial(n) for n in range(N)] for m in range(N)])
            coeffs = [log(b)**n/factorial(n) for n in xrange(N)]
        else:
            #too slow
            #c = b**x0
            #C = Matrix([ [log(b)**n/factorial(n)*sum([binomial(m,k)*k**n*c**k*(-x0)**(m-k) for k in range(m+1)]) for n in range(N)] for m in range(N)])
            coeffs = [b**x0-x0]+[b**x0*log(b)**n/factorial(n) for n in xrange(1,N)]

        def psmul(A,B):
            N = len(B)
            return [sum([A[k]*B[n-k] for k in xrange(n+1)]) for n in xrange(N)]
        
        C = Matrix(R,N)
        row = vector(R,[1]+(N-1)*[0])
        C[0] = row
        for m in xrange(1,N):
            row = psmul(row,coeffs)
            C[m] = row
  
        print "Carleman matrix created."

        #numeric matrix and eigenvalues
        #self.CM = C.n(iprec) #n seems to reduce to a RealField
        self.CM = C

        self.eigenvalues = self.CM.eigenvalues()
        print "Eigenvalues computed."

        self.IM = None
        self.calc_IM()
        print "Iteration matrix computed."
        self.coeffs_1 = self.IM * vector([1]+[(1-x0)**n for n in range(1,N)])
        if x0 == 0:
            self.coeffs_0 = self.IM.column(0)
        else:
            self.coeffs_0 = self.IM * vector([1]+[(-x0)**n for n in range(1,N)])
        #there would also be a method to only coeffs_0 with x0,
        #this would require to make the offset -1-slog(0)
       
        self.L = None

    def calc_IM(self):
        eigenvalues = self.eigenvalues
        iprec = self.iprec
        CM = self.CM
        
        ev = [ e.n(iprec) for e in eigenvalues]
        n = len(ev)
    
        Char = [CM - ev[k] * identity_matrix(n) for k in range(n)]
    
        #product till k-1
        prodwo = n * [0]
        prod = vector([0,1]+(n-2)*[0]);
        for k in range(n):
            prodwo[k] = prod
            for i in range(k+1,n):
                prodwo[k] = prodwo[k] * Char[i]
    
            if k == n:
                break
            prod = prod * Char[k]
    
        sprodwo = n * [0]
        for k in range(n):
            if k == 0:
                sprodwo[k] = ev[k] - ev[1]
                start = 2
            else:
                sprodwo[k] = ev[k] - ev[0]
                start = 1
            
            for i in range(start,n):
                if not i == k:
                    sprodwo[k] = sprodwo[k] * (ev[k]-ev[i])
    
        self.IM = Matrix([1/sprodwo[k]*prodwo[k] for k in range(n)])
        return self

    def _in_prec(self,x):
        if isinstance(x,float) or isinstance(x,int) or isinstance(x,Integer):
           return RealField(self.iprec)(x)
        return x

    def calc_slog(self):
        RP = FormalPowerSeriesRing(RealField(self.iprec))
        ev = self.eigenvalues
        a1 = self.coeffs_1
        N = self.N

        #how can this be made picklable?
        class _SexpCoeffs1(FormalPowerSeries0):
            def coeffs(self,n):
               if n==0: return 0
               return sum([a1[k]*log(ev[k])**n for k in xrange(N)])/factorial(n)
        class _SexpCoeffs0(FormalPowerSeries0):
            def coeffs(self,n):
               if n==0: return 0
               return sum([a0[k]*log(ev[k])**n for k in xrange(N)])/factorial(n) 

        self.sexp_coeffs_1 = _SexpCoeffs1(RP,min_index=1)
        self.slog_coeffs_1 = self.sexp_coeffs_1.inv()

        if self.L != None:
            return self.L
        b = self.b
        iprec = self.iprec

        if b > (e**(1/e)).n(iprec):
            L = ComplexField(iprec)(0.5)
            for n in range(100):
                L = log(L)/log(b)
        else:
            L = RealField(iprec)(0)
            for n in range(100):
                L = b**L
            
        self.L = L
        return self
        
    def sexp_1t(self,t,n=None):
        if n == None:
            n = self.N
        return 1+self.sexp_coeffs_1.polynomial(n)(t)

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

    def slog(self,z,n=None):
        slog = self.slog
        b = self.b

        if n == None:
            n = self.N
        if self.cmp_ir(z) == -1:
            return slog(b**z)-1
        if self.cmp_ir(z) == +1:
            return slog(log(z)/log(b))+1
        return self.slog_1t(z)

    def slog_1t(self,t,n=None):
        if n == None:
            n = self.N
        return self.slog_coeffs_1.polynomial(n)(t-1)

    def sexp_1_raw(self,t):
        x0 = self.x0
        return x0+vector([ v**t for v in self.eigenvalues ]) * self.coeffs_1
        
    def sexp_1_raw_deriv(self,t):
        return vector([ ln(v)*v**t for v in self.eigenvalues ]) * self.coeffs_1

    def sexp_1(self,t):
        t = self._in_prec(t)
        sexp = self.sexp_1
        b = self.b
        IM = self.IM
        N = self.N

        #development point 0 convergence radius 2
        if real(t)>1:
            return b**(sexp(t-1))
        if real(t)<0:
            #sage bug, log(z,b) does not work for complex z
            return log(sexp(t+1))/log(b)
	return self.sexp_1_raw(t)

    def sexp_0_raw(self,t):
        x0 = self.x0
        return b**(x0+vector([ v**t for v in self.eigenvalues ])*self.coeffs_0)
	

    def sexp_0(self,t):
        #convergence radius 1
        t = self._in_prec(t)
        sexp = self.sexp_0
        b = self.b

        #development point -1 convergence radius 1
        if real(t)>1:
            return b**(sexp(t-1))
        if real(t)<0:
            #sage bug, log(z,b) does not work for complex z
            return log(sexp(t+1))/log(b)
	return self.sexp_0_raw(t)

    def sexp(self,t):
        if self.prec != None:
            return self.sexp_1(t).n(self.prec)
        return self.sexp_1(t)

    def calc_prec(self):
        if self.prec != None:
            return self.prec

        mp0 = MatrixPowerSexp(self.bsym,self.N-1,iprec=self.iprec,x0=self.x0sym)

        sexp_precision=RR(1)*log(abs(self.sexp_1(0.5)-mp0.sexp_1(0.5)),2.0)
        self.prec = (-sexp_precision).floor()
        print "sexp precision: " , self.prec

        cprec = self.prec+ceil(log(self.N)/log(2.0))

        #self.eigenvalues = [ ev.n(cprec) for ev in self.eigenvalues ]
        #self.IM = self.IM.n(cprec)
        #self.b = self.bsym.n(cprec)
        return self

    def backup(self):
        path = self.path
        prec = self.prec

        print "Writing to '" + path + ".sobj'."
        save(self,path)
        if prec != None: save(prec,path+"_prec"+repr(prec))
        return self
