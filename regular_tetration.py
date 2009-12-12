from sage.functions.log import log
from sage.misc.functional import n as num
from sage.rings.complex_field import ComplexField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.real_mpfr import RR, RealField
import mpmath

class RegularTetration:
    def __init__(self,b,N,fixpoint_number=0,iprec=512,prec=None):
        """
	Counting fixpoints as follows:
        For b<e^(1/e): 
	  0 denotes the lower fixpoint on the real axis,
          1 denotes the upper fixed point on the real axis,
	  2 denotes the fixpoint in the upper halfplane closest to the real axis, 
          3 the second-closest, etc

	For b>e^(1/e): 
	  1 denotes the fixpoint in the upper halfplane closest to the real axis,
          2 the second-closest fixed point, etc.
        """

        self.bsym = b
        self.N = N
        self.iprec = iprec
        self.prec = prec
        self.fixpoint_number = fixpoint_number

        bname = repr(b).replace('.',',')
        if b == sqrt(2):
           bname = "sqrt2"
        if b == e**(1/e):
           bname = "eta"

        b = num(b,iprec)
        self.b = b

        self.path = "savings/islog_%s"%bname + "_N%04d"%N + "_iprec%05d"%iprec + "_fp%d"%fixpoint_number


        if iprec != None:
            b = num(b,iprec)
            self.b = b
        else:
            if b == e and x0 == 0:
                R = QQ
            else:
                R = SR
        self.R = RealField(iprec)
        self.C = ComplexField(iprec)

	mpmath.mp.prec = iprec
        L = mpmath.lambertw(-mpmath.ln(b),-fixpoint_number)/(-mpmath.ln(b))
        L = ComplexField(iprec)(L.real,L.imag)
        self.L = L

        self.r = 0.5



        R = RealField(iprec)
        FR = FormalPowerSeriesRing(R)
        [rho,ps] = FR.Dec_exp(FR([0,log(b)])).rmul(L).abel_coeffs()
        PR = PolynomialRing(R,'x')
        self.rho = rho
        self.slogpoly = ps.polynomial(N)

        self.c = 0
        if fixpoint_number == 0:
            #slog(0)==-1
	    self.c = -1 - self.slog(0.0)                   


    def slog_raw(self,z): 
        z = num(z,self.iprec)
        return self.c + self.rho*log(z-self.L) + self.slogpoly(z-self.L)
        
        
    def slog(self,z):
        z = num(z,self.iprec)
        if abs(z-self.L) > self.r:
            if self.fixpoint_number == 0:
                return self.slog(self.b**z)-1
            else:
                return self.slog(log(z)/log(self.b))+1

        return self.slog_raw(z)
