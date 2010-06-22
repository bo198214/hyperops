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
    def __init__(self,b=sqrt(2),fixpoint_number=0,u=None,prec=53,iprec=None,N=5,direction=-1,debug=0):
        """
        for the numbering of fixed points see function exp_fixpoint

        u is the initial value such that slog(u)=0 and sexp(0)=u
        for the attracting fixed point it defaults to u=1
        otherwise it is undetermined

        direction can be +1 (real values when approaching from the right of the fixpoint) 
        or -1 (real values when approaching from the left of the fixed point)
        """

        if debug >= 1:
            if b==sqrt(2): print 'b:',b
            if fixpoint_number==0: print 'fixpoint_number:',fixpoint_number
            if prec==53: print 'prec:',prec
            if N==5: print 'N:',N
            if direction==-1: print 'direction:',direction

        self.bsym = b
        self.N = N
        if iprec==None:
            iprec=prec+10
            if debug>=1: print 'iprec:',iprec
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
        if self.bsym == eta and abs(fixpoint_number) <= 1:
            self.parabolic = True
            if direction == +1:
                self.attracting = False
            if direction == -1:
                self.attracting = True

        if b <= eta and abs(fixpoint_number) <= 1:
            R = RealField(iprec)
        else:
            R = ComplexField(iprec)
        self.R = R

        if self.parabolic:
            fp = R(e) #just for not messing it into a complex number
        else:
            fp = exp_fixpoint(b,fixpoint_number,prec=iprec)

        self.fp = fp

        self.direction = direction

        FR = FormalPowerSeriesRing(R)
        fps = FR.Dec_exp(FR([0,log(b)])).rmul(fp)
        if self.parabolic:
            fps=fps.set_item(1,1).reclass()
            
        if debug>=1: print "fp:",fp

        [rho,ps] = fps.abel_coeffs()
        if debug>=2: print 'fps:',fps
        if debug>=2: print 'rho:',rho
        if debug>=2: print 'abel_ps:',ps
            
        PR = PolynomialRing(R,'x')
        self.slogpoly = ps.polynomial(N)
        if debug>=2: print self.slogpoly

        self.slog_raw0 = lambda z: rho*log(direction*(z-self.fp)) + self.slogpoly(z-self.fp)

        #slog(u)==0
        self.c = 0
        if self.attracting and direction==-1 and u==None:
            u=1
            if debug>=1: print 'u:',u
            
        if not u==None:
            self.c = -self.slog(u)                   
            pass
        
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
            #TODO logarithms branches should be chosen to converge to the fixed point
            xn = log(xn)/lnb

        yn = self.slog_raw0(xn)
  
        if self.attracting:
            d = abs(yn - (yp+1))
        else:
            d = abs(yn - (yp-1))

        if debug >=2: print n,":","d:",d.n(20),"yn:",yn,"xn:",xn
        
        if xp == xn or d == 1:
            if debug>=0: 
		print "slog: increase iprec(",iprec,") or decrease prec(",prec,") to get a result for x:",x,"b:",b
            return NaN
        
          
        if d<err: 
            res = self.c + yn.n(prec)

            if self.attracting:
                res -= n
            else:
                res += n
  
            if debug>=1: print 'n:',n,'d:',d.n(20),'err:',err,'res:',res
            return res

