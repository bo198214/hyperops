from sage.functions.log import log
from sage.misc.functional import n as num
from sage.rings.complex_field import ComplexField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.real_mpfr import RR, RealField
import mpmath

def exp_fixpoint(b=e,k=1,prec=53,iprec=None):
    """
    Counting fixpoints as follows:

    For b<=e^(1/e): 
      0 denotes the lower fixpoint on the real axis,
      1 denotes the upper fixed point on the real axis,
      2 denotes the fixpoint in the upper halfplane closest to the real axis, 
      3 the second-closest, etc

    For b>e^(1/e): 
      1 denotes the fixpoint in the upper halfplane closest to the real axis,
      2 the second-closest fixed point, etc.

    Or in other words order the repelling fixed points of the upper halfplane 
    by their distance from the real axis, give the closest fixed point the number 1.
    The attracting fixed point (existent only for b<e**(1/e)) gets index 0.

    Fixpoint k mirrored into the lower halfplane gets index -k.
    """
    if iprec==None:
        iprec=prec+10
    b=num(b,iprec)

    if k==0:
        assert b <= e**(1/e), "b must be <= e**(1/e) for fixpoint number 0, but b=" + repr(b)
    if k>=0:
        branch = -k
    elif b <= e**(1/e) and k==-1:
        branch = -1
    else:
        branch = -k-1

    mpmath.mp.prec = iprec
    fp = mpmath.lambertw(-mpmath.ln(b),branch)/(-mpmath.ln(b))
    if type(fp) == sage.libs.mpmath.ext_main.mpf:
      return num(fp,prec)
    return ComplexField(prec)(fp.real,fp.imag)

class RegularTetration:
    def __init__(self,b=sqrt(2),fixpoint_number=0,prec=53,iprec=None,N=5,angle_real=pi):
        """
        for the numbering of fixed points see function exp_fixpoint
        """

        self.bsym = b
        self.N = N
        if iprec==None:
            iprec=prec+10
        self.iprec = iprec
        self.prec = prec
        self.fixpoint_number = fixpoint_number

        eta = e**(1/e)

        bname = repr(b).strip('0').replace('.',',')
        if b == sqrt(2):
           bname = "sqrt2"
        if b == eta:
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

        self.attracting = False
        if b < eta and fixpoint_number == 0:
            self.attracting = True

        self.parabolic = False
        if b == eta and fixpoint_number == 0:
            self.parabolic == True
            if angle_real == 0:
                self.attracting = False
            if angle_real == pi:
                self.attracting = True

        if b <= eta and abs(fixpoint_number) <= 1:
            R = RealField(iprec)
        else:
            R = ComplexField(iprec)
        self.R = R

        fp = exp_fixpoint(b,fixpoint_number,prec=iprec)
        self.fp = fp
        print "fp:",fp

        if b <= eta and fixpoint_number == 0:
            r = abs(fp-exp_fixpoint(b,1))
        else:
            r1 = abs(fp-exp_fixpoint(b,fixpoint_number+1))
            #r2 = abs(fp-exp_fixpoint(b,fixpoint_number-1))
            #r = min(r1,r2)
            r = 0.5

        self.r = r

        if angle_real == pi:
            self.direction = -1
        elif angle_real == 0:
            self.direction = 1
        else:
            self.direction = exp(ComplexField(self.iprec)(0,angle_real))


        FR = FormalPowerSeriesRing(R)
        [rho,ps] = FR.Dec_exp(FR([0,log(b)])).rmul(fp).abel_coeffs()
        PR = PolynomialRing(R,'x')
        self.rho = rho
        self.slogpoly = ps.polynomial(N)

        self.slog_raw0 = lambda z: self.rho*self.log(z-self.fp) + self.slogpoly(z-self.fp)

        self.c = 0
        if fixpoint_number == 0:
            #slog(0)==-1
	    #self.c = -1 - self.slog(0.0)                   
            pass
        

    def log(self,z):
        return log(z*self.direction) 

    def slog_raw(self,z): 
        z = num(z,self.iprec)
        return self.c + self.slog_raw0(z)
        
        
    def slog_orig(self,z):
        z = num(z,self.iprec)
        if abs(z-self.fp) > self.r/2:
            if self.attracting:
                return self.slog(self.b**z)-1
            else:
                return self.slog(log(z)/log(self.b))+1

        return self.slog_raw(z)

    def slog(self,x,debug=0):
      iprec=self.iprec
      prec=self.prec
      b = self.b
      z0= self.fp
      a = ln(z0)

      xin = x
      err=2.0**(-prec)
      if debug>=1: print 'N:',self.N,'iprec:',iprec,'prec:',prec,'b:',b,'z0:',z0,'a:',a,'err:',err
      lnb = ln(b)
      n = 0
      xn = num(x,iprec)
      yn = self.slog_raw0(xn)
      while True:
        yp=yn
        xp=x
        n += 1

        if self.attracting:
            xn = b**xn
        else:
            xn = log(xn)/lnb

        yn = self.slog_raw0(xn)
  
        if self.attracting:
            d = abs(yn - (yp+1))
        else:
            d = abs(yn - (yp-1))

        if debug >=2: print n,":","d:",d.n(20),"yn:",yn,"xn:",xn
        
        if xp == xn or d == 1:
            print "iprec may be to low or prec maybe too high for x:",x,"b:",b
            return NaN
        
          
        if d<err: 
            res = self.c + yn.n(prec)

            if self.attracting:
                res -= n
            else:
                res += n
  
            if debug>=1: print 'n:',n,'d:',d.n(20),'err:',err,'res:',res
            return res

