from sage import all
from formal_powerseries import FormalPowerSeriesRing
from mpmath import lambertw, mp, ln as mpln
from sage.functions.log import log, ln
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.real_mpfr import RR, RealField


class Balanced:

  def __init__(self,n,symbolic=False,iprec=53,prec=53,r=0.5):
    self.n = n
    self.r = r
    self.iprec = iprec
    self.prec = prec
    mp.prec = iprec
  
    L = PolynomialRing(QQ,'ln2')
    ln2 = L.gen()
    self.ln2 = ln2
    FPL = FormalPowerSeriesRing(L)
    self.FPL = FPL
  
    R = RealField(iprec)
    self.R = R
    FPR = FormalPowerSeriesRing(R)
    self.FPR = FPR
  
    def log2(x):
      return ln(x)/R(ln(2))

    if n==1:
      self.hfop = lambda x,y: log2(R(2)**x+R(2)**y)
      self.hp = FPL([1,1])
      self.hf = lambda x: x+1
      self.hfi = lambda x: x-1
      #self.op = lambda x,y: x+y 
    elif n==2:
      self.hfop = lambda x,y: x + y
      self.hp = FPL([0,2])
      self.hf = lambda x: R(2)*x
      self.hfi = lambda x: x/R(2)
      #self.op = lambda x,y: x*y # 2**(log2(x)+log2(y))
    elif n==3:
      self.hfop = lambda x,y: x*(R(2)**y)
      self.hp = FPL.Exp(FPL([0,ln2])) * FPL([0,1])
      self.hp.reclass()
      self.hpr = FPR.Exp(FPR([0,R(ln(2))])) * FPR([0,1])
      self.hpr.reclass()
      self.hf = lambda x: R(x)*R(2)**R(x)
      self.hfi = lambda y: R(lambertw(R(y)*R(ln(2))))/R(ln(2))
    else:
      self.G = Balanced(n-1,symbolic=symbolic,iprec=iprec)
      self.hpop = lambda y: self.G.hp.it(y)
      self.hp = self.G.hp.selfit()
      self.hp.reclass()
      if symbolic:
        def subs(e): 
          if type(e) == int:
            return R(e) 
          return e.subs(R( log( 2 ) ))
        self.hprop = lambda y: FPR.by_formal_powerseries(self.hpop(y),subs)
        self.hpr = FPR.by_formal_powerseries(self.hp, subs)
      else:
        self.hprop = lambda y: self.G.hpr.it(y)
        self.hpr = self.G.hpr.selfit()
      self.hpr.reclass()
      self.hfop = self.f()
      self.hf = lambda x: self.hfop(x,x)
      #self.hfi = self.f(self.hp.inv())

    self.op = lambda x,y: R(2)**(self.hfop(log2(x),log2(y)))
  
  
  def f(self):
    r = self.r
    err = 2.0**(-self.prec)
    g = self.G.hf
    gi = self.G.hfi
    def res(x,y):
      x = self.R(x)
      y = self.R(y)
      hpy = self.hprop(y)
      n = 0
      while x > r:
        x = gi(x)
        n+=1
        #print 'n',n,x

      j = 1
      xtj = x
      s = 0
      min = 1000000000000000 #todo
      d = hpy[j]*xtj
      mincount = 0
      s1 = None
      while mincount <= 1 and abs(d) > err/2:
        #print 'j',j,s,'d',d,hpy[j],xtj
        j+=1
        if d == 0: continue
        s += d
        xtj *= x
        if abs(d) < min: 
          min = abs(d)
          mincount = 0
        else: 
          s1 = s
          mincount += 1
        d = hpy[j]*xtj
        
      if s1 != None:
        s=s1
      print 'j',j,'s',s,'d',d,'mincount',mincount
    
    
      for k in range(n):
        s = g(s)
        print 's',s

      return s
    return res
  
  def bal(n):
    if n == 1:
      return lambda x,y: x+y
    else:
      def b(x,y):
        hrp.it(y)


b1 = Balanced(1)
b2 = Balanced(2)
b3 = Balanced(3)
b4 = Balanced(4)
