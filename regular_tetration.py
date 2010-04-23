from sage.functions.log import log
from sage.misc.functional import n as num
from sage.rings.complex_field import ComplexField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.real_mpfr import RR, RealField
import mpmath

class RegularTetration:
    def __init__(self,b,N,iprec=512,fixpoint_number=0,prec=None,angle_real=pi):
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

        bname = repr(b).strip('0').replace('.',',')
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
        R = RealField(iprec)
        C = ComplexField(iprec)
        self.R = R
        self.C = C

	mpmath.mp.prec = iprec
        L = self.fp(fixpoint_number)
        self.L = L


        if b <= e**(1/e) and fixpoint_number == 0:
            r = abs(L-self.fp(1))
        else:
            r1 = abs(L-self.fp(fixpoint_number+1))
            r2 = abs(L-self.fp(fixpoint_number-1))
            r = min(r1,r2)

        self.r = r
        self.phi = angle_real

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

    def fp(self,k=1):
        b=self.b
        iprec = self.iprec
        L = mpmath.lambertw(-mpmath.ln(b),-k)/(-mpmath.ln(b))
        return ComplexField(iprec)(L.real,L.imag)

    def log(self,z):
        return log(z*exp(CC(0,-self.phi))) 

    def slog_raw(self,z): 
        z = num(z,self.iprec)
        return self.c + self.rho*self.log(z-self.L) + self.slogpoly(z-self.L)
        
        
    def slog(self,z):
        z = num(z,self.iprec)
        if abs(z-self.L) > self.r/2:
            if self.fixpoint_number == 0:
                return self.slog(self.b**z)-1
            else:
                return self.slog(log(z)/log(self.b))+1

        return self.slog_raw(z)
