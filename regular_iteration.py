from sage.functions.log import ln
from sage.functions.other import sqrt
from sage.misc.functional import n as num
from sage.rings.complex_field import ComplexField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.real_mpfr import RR, RealField
from sage.symbolic.constants import e,NaN, pi, I
from sage.functions.log import log
from exp_fixpoint import exp_fixpoint
from sage.rings.rational_field import QQ
from sage.symbolic.ring import SR


class RegularIterate:
    def __init__(self,f,fi,exponent,fps=None,fixpoint=0,z0=0,u=None,prec=53,iprec=None,N=5,direction=-1,debug=0):
        self.attracting  = False
        self.fp = fixpoint

        self.prec = prec

        self.f = f
        self.fi = fi
        self.N = N

        if iprec == None:
             iprec = prec + 10
        self.iprec = iprec

        R = RealField(iprec)
        F = FormalPowerSeriesRing(R)

        if fps == None:
            p = F(f)
        else:
            p = F.by_formal_powerseries(fps)
            
        pit = p.it(exponent)

        self.iterate_poly = pit.polynomial(N)
        self.iterate_raw0 = lambda z: self.fp + self.iterate_poly(z-self.fp)

    def iterate(self,x,debug=0):
      iprec=self.iprec
      prec=self.prec
      z0= self.fp

      xin = x
      err=2.0**(-prec)
      if debug>=1: print('N:', self.N, 'iprec:', iprec, 'prec:', prec, 'z0:', z0, 'err:', err)
      #lnb = b.log()
      n = 0
      xn = num(x,iprec)
      yn = self.iterate_raw0(xn)
      while True:
        yp=yn
        xp=x
        n += 1

        if self.attracting:
            xn = self.f(xn)
        else:
            xn = self.fi(xn)

        yn = self.iterate_raw0(xn)

        if self.attracting:
            for k in range(n):
                yn = self.fi(yn)
        else:
            for k in range(n):
                yn = self.f(yn)
  
        if self.attracting:
            d = abs(yn - yp)
        else:
            d = abs(yn - yp)

        if debug >=2: print(n,":","d:",d.n(20),"yn:",yn,"xn:",xn)
        
        if xp == xn:
            if debug>=0: 
                print("slog: increase iprec(",iprec,") or decrease prec(",prec,") to get a result for x:",x)
            return NaN
        
          
        if d<err: 
            res = yn.n(prec)

            if debug>=1: print('res:',res,'n:',n,'d:',d.n(20),'err:',err )
            return res
        
        

class RegularSlog:
    def __init__(self,f,fixpoint_number=0,z0=0,u=None,prec=53,iprec=None,N=5,direction=-1,debug=0):
        """
        for the numbering of fixed points see function exp_fixpoint

        u is the initial value such that slog(u)=0 and sexp(0)=u
        for the attracting fixed point it defaults to u=1
        otherwise it is undetermined

        direction can be +1 (real values when approaching from the right of the fixpoint) 
        or -1 (real values when approaching from the left of the fixed point)
        """

        if debug >= 1:
            if b==sqrt(2): print('b:', b)
            if fixpoint_number==0: print('fixpoint_number:', fixpoint_number)
            if prec==53: print('prec:', prec)
            if N==5: print('N:', N)
            if direction==-1: print('direction:', direction)

        bsym = b
        self.bsym = bsym
        self.N = N
        if iprec==None:
            iprec=prec+10
            if debug>=1: print('iprec:', iprec)
        self.iprec = iprec
        self.prec = prec
        self.fixpoint_number = fixpoint_number

        eta = e**(1/e)

        bname = repr(bsym).strip('0').replace('.',',')
        if bsym == sqrt(2):
           bname = "sqrt2"
        if bsym == eta:
           bname = "eta"

        self.lnb = num(ln(bsym),iprec)

        b = num(bsym,iprec)
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

        self.real_fp = False
        if b <= eta and abs(fixpoint_number) <= 1:
            self.real_fp = True

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
        fps = FR.Dec_exp(FR([0,b.log()])).rmul(fp)
        if self.parabolic:
            fps=fps.set_item(1,1).reclass()
            
        if debug>=1: print("fp:", fp)

        [rho,ps] = fps.abel_coeffs()
        if debug>=2: print('fps:', fps)
        if debug>=2: print('rho:', rho)
        if debug>=2: print('abel_ps:', ps)

        PR = PolynomialRing(R,'x')
        self.slogpoly = ps.polynomial(N)
        if debug>=2: print(self.slogpoly)

        self.slog_raw0 = lambda z: rho*(direction*(z-self.fp)).log() + self.slogpoly(z-self.fp)

        #slog(u)==0
        self.c = 0
        if self.attracting and direction==-1 and u==None:
            u=1
            if debug>=1: print('u:', u)

        if not u==None:
            self.c = -self.slog(u)                   
            pass
        
    def logb(self,z):
        """
        Logarithm with branch cut such that for imaginary values y:
          -pi < y <= pi for real fixpoint
          otherwise:
          2*pi*(k-1) <= y <  2*pi*k     for k>=1
          2*pi*k     <  y <= 2*pi*(k+1) for k<=-1

          where k is the fixpoint_number
        """
        k = self.fixpoint_number
        if self.real_fp:
            res = z.log()
        elif k>=1:
            res = (log(-z.conjugate())-num(I*(2*pi*k-pi),self.iprec)).conjugate()
        elif k<=-1:
            res = log(-z)+num(I*(2*pi*k+pi),self.iprec)

        return res/self.lnb

    def slog(self,x,debug=0):
      iprec=self.iprec
      prec=self.prec
      b = self.b
      z0= self.fp
      a = z0.log()

      xin = x
      err=2.0**(-prec)
      if debug>=1: print('N:',self.N,'iprec:',iprec,'prec:',prec,'b:',b,'z0:',z0,'a:',a,'err:',err)
      #lnb = b.log()
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
            xn = self.logb(xn)

        yn = self.slog_raw0(xn)
  
        if self.attracting:
            d = abs(yn - (yp+1))
        else:
            d = abs(yn - (yp-1))

        if debug >=2: print(n,":","d:",d.n(20),"yn:",yn,"xn:",xn)
        
        if xp == xn or d == 1:
            if debug>=0: 
                print("slog: increase iprec(",iprec,") or decrease prec(",prec,") to get a result for x:",x,"b:",b)
            return NaN
        
          
        if d<err: 
            res = self.c + yn.n(prec)

            if self.attracting:
                res -= n
            else:
                res += n
  
            if debug>=1: print('res:',res,'n:',n,'d:',d.n(20),'err:',err)
            return res
