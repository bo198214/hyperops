from math import isnan
from sage.functions.other import real, imag
from sage.rings.real_mpfr import RR, RealField


class NotConverged(BaseException):
    pass


def itn(f, z, N, eps=None, fp=0, iterates=None):
    """
    with eps=None iterates exactly N times the function f on z
    if eps is not None iterates until the value is inside eps-disc around fp
    but at most N times.
    If the result is not inside the eps-disc around fp then
    throw NotConverged exception
    otherwise it returns the tupel (n,z)
    n being the number of iterations used
    z being the result of the iterations
    """
    if iterates is not None:
        iterates.append(z)
    n=0
    for n in range(N):
        if iterates is not None:
            iterates.append(z)
        if eps is not None and abs(z-fp) < eps:
            return n, z
        if isnan(real(z)) or isnan(imag(z)):
            raise NotConverged(z, n)
        z = f(z)
    if eps is None:
        return z
    else:
        raise NotConverged(RR(abs(z-fp)), eps, n)