from sage.misc.functional import n as num
from sage.rings.complex_field import ComplexField
from sage.symbolic.constants import e
import mpmath
import sage.libs.mpmath.ext_main

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

