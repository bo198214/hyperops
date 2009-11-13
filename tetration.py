from sage.rings.formal_powerseries import FormalPowerSeriesRing
import mpmath

def mpc2C(z,prec=53):
  R = RealField(prec)
  C = ComplexField(prec)
  return C(R(z.real),R(z.imag))
  
def tet(b,t,prec=500,n=50):
  N = n
  oprec = (b+t).prec()
  C = ComplexField(prec)
  FC = FormalPowerSeriesRing(C)
  lnb = log(C(b))
  mpmath.mp.prec = prec
  lna = mpc2C(- mpmath.lambertw( - lnb))
  a = exp(lna)
  a2 = mpc2C( mpmath.exp(-mpmath.lambertw(-lnb,-1)))
  r = abs(a2-a)
  zn = 1
  n=0
  while abs(zn-a) > r:
    zn = b**zn
    n+=1
    # print 'zn',n,zn
  # print zn
  h = FC.Dec_exp.rmul(lna)
  # w = ComplexField(oprec)(a+h.it(t).polynomial(N)(lnb*(1-a))/lnb)
  # print 'w',w
  wn = ComplexField(oprec)(a+h.it(t).polynomial(N)(lnb*(zn-a))/lnb)
  for k in range(1,n+1):
    wn = log(wn)/lnb
    # print 'wn',k,wn
  return wn

#Shell Thron boundary
st = lambda z: exp(z*exp(-z))
circ = lambda t: exp(CC(0,2*pi*t))
stb = lambda t: st(circ(t))
