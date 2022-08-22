from sage.rings.real_mpfr import RR, RealField, RealField_class
from sage.functions.log import log

class NotConverged(BaseException):
    pass


def itn(f, z, fp, n_max, eps=None, prec=53):
    """
    Iterate z=f(z) until abs(z-z0)<eps or n>max_n
    and then return z,n
    If eps is None then exactly iterate n_max times
    Operations are executed with precision prec
    """
    for n in range(n_max):
        z = f(z)
        if eps is not None and abs(z - fp) < eps:
            return z,n
    if eps is None:
        return z
    else:
        raise NotConverged(abs(z - fp),z,n)


def iterate_regular_hyperbolic(fi,f,p,z,fp,fpd,nmax=1000,eps=0.0001,info=None,iterates=None,prec=53):
    pass


def iterate_regular_hyperbolic_ecalle(fi, f, p, z, fp, ps0, nmax=1000, eps=0.0001, info=None, iterates=None, prec=53):
    pass


def abel_regular_parabolic_ecalle(f, z, fp, ps0, q, direction=1, ntrunc=100, nmax=1000, eps=0.0001, info=None, iterates=None, prec=53):
    ps0q = ps0.it(q).reclass()
    det = ps0q[ps0q.valit()+1]
    coeffs = ps0q.abel_coeffs()
    abel_trunc = lambda x: (coeffs[0]*log(-x*direction) + coeffs[1].polynomial(ntrunc,R=RealField(prec))(x))

    z,n = itn(f,z,fp,nmax,eps)
    if info is not None:
        info["n"] = n
        info["d"] = abs(z-fp)
    return abel_trunc(z-fp) + fp - n*direction


