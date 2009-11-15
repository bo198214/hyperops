from sage.rings.formal_powerseries import FormalPowerSeriesRing
import mpmath
from scipy.optimize import fmin, brenth

def mpc2C(z,prec=53):
  R = RealField(prec)
  C = ComplexField(prec)
  return C(R(z.real),R(z.imag))
  

def expit(b,t,z,prec=100,n=10,r=None):
  N = n
  oprec = (b+t).prec()

  if b == 1:
    return ComplexField(oprec)(1)

  C = ComplexField(prec)
  FC = FormalPowerSeriesRing(C)
  lnb = log(C(b))
  mpmath.mp.prec = prec
  lna = mpc2C(- mpmath.lambertw( - lnb))
  a = exp(lna)
  # print 'a',a,'|lna|',abs(lna)
  if r == None:

    r = 1 - abs(lna)

    if not r>0: 
      print 'lna',lna,'r',r,'dist','z',z,'|lna-lnz|',abs(lna-log(z))
      a2 = mpc2C( mpmath.exp(-mpmath.lambertw(-lnb,-1)))
      # print 'a',a2
      r = abs(a2-a)
    
  zn = z
  n=0
  while abs(log(zn)-lna) > r:
    zn = b**zn
    n+=1
  #  print 'zn',n,zn
  # print zn
  h = FC.Dec_exp.rmul(lna)
  # w = ComplexField(oprec)(a+h.it(t).polynomial(N)(lnb*(1-a))/lnb)
  # print 'w',w
  wn = ComplexField(oprec)(a+h.it(t).polynomial(N)(lnb*(zn-a))/lnb)
  for k in range(1,n+1):
    wn = log(wn)/lnb
    # print 'wn',k,wn
  return wn

#the circle with center (0.84,0.801), radius 1.2 
#lies inside the tsr for y > 0.7
#the circle with center (1.22,0.77), radius 0.8,
#lies inside the tsr for 0<y<0.7

def d(b,**kwargs): 
  f = lambda z: expit(b,0.5,z,**kwargs)
  res = abs(f(f(1.0))-b)
  if res > 10**(-5):
    print 'b',b,'d(b)',res
  return res

def tet(b,t,**kwargs):
  return expit(b,t,1,**kwargs)

def shrinked_circ(t):
  r = 0.85
  return r*exp(CC(0,2*pi*(float(t)-0.25)))+CC(r,r)

class Region:
  def __init__(self,factor=0):
    self.factor = factor
    circ = lambda t: exp(CC(0,pi*float(t)))
    #Shell Thron boundary
    st = lambda z: exp(z*exp(-z))
    self.stb0 = lambda t: st(circ(t))
    self.stbtymax = fmin(lambda t: -self.stb(t).imag(), 0.5)[0] 
    self.stbtxmax = fmin(lambda t: -self.stb(t).real(), 0.1)[0] 
    self.stbtxmin = fmin(lambda t: self.stb(t).real(), 0.6)[0]

  def stb(self,t):
    factor = self.factor
    stb0 = self.stb0
    
    ret = (1-factor)*stb0(t)+factor*shrinked_circ(t)
    return ret
  
  def yints(self,x):
    stb = self.stb
    stbtymax = self.stbtymax
    stbtxmax = self.stbtxmax
    stbtxmin = self.stbtxmin

    xmax = stb(stbtxmax).real()
    xmin = stb(stbtxmin).real()
    eta0 = stb(1)
    eta1 = stb(0)
    if x <= xmin or x>=xmax:
      return []
    b = stb(brenth(lambda t: stb(t).real() - x, stbtxmax,stbtxmin)).imag()
    if eta0 <= x and x <= eta1:
      a = 0
    else:
      if eta1 < x:
        a = stb(brenth(lambda t: stb(t).real() - x, 0,stbtxmax)).imag()
      if x < eta0:
        a = stb(brenth(lambda t: stb(t).real() - x, stbtxmin,1)).imag()
    return [(a,b)]
    
  def xints(self,y):
    stb = self.stb
    stbtymax = self.stbtymax
    stbtxmax = self.stbtxmax
    stbtxmin = self.stbtxmin
    
    ymax = stb(stbtymax).imag()
    if y <= 0 or y>=ymax:
      return []
    a = stb(brenth(lambda t: stb(t).imag() - y, stbtymax,1)).real()
    b = stb(brenth(lambda t: stb(t).imag() - y, 0,stbtymax)).real()
    return [(a,b)]
  
  def region(self,xmin=None,xmax=None,ymin=None,ymax=None):
    stb = self.stb
    stbtymax = self.stbtymax
    stbtxmax = self.stbtxmax
    stbtxmin = self.stbtxmin
    xints = self.xints
    yints = self.yints

    if xmin == None:
      xmin = stb(stbtxmin).real()
    if xmax == None:
      xmax = stb(stbtxmax).real()
    xrange=(xmin,xmax)
  
    if ymin == None:
      ymin = 0
    if ymax == None:
      ymax = stb(stbtymax).imag()
    yrange=(ymin,ymax)
  
    return (xrange,yrange,yints,xints)
  
# conformal_region_plot(lambda z: z, region(0.1,xmin=0.9)) + complex_parametric_plot(stb)
