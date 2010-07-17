from sage.functions.log import log, ln
from sage.functions.other import sqrt,real,imag,ceil,floor
from sage.functions.trig import tan
from sage.matrix.constructor import Matrix, identity_matrix
from sage.misc.functional import n as num
from sage.misc.persist import save
from sage.modules.free_module_element import vector
from sage.rings.arith import factorial, binomial
from sage.rings.complex_field import ComplexField
from sage.rings.formal_powerseries import FormalPowerSeriesRing
from sage.rings.integer import Integer
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ
from sage.rings.real_mpfr import RR, RealField
from sage.symbolic.constants import e
from sage.symbolic.ring import SR

from sage.hyperops.exp_fixpoint import exp_fixpoint

class IntuitiveTetration:
    def __init__(self,b,N,iprec=512,u=None,x0=0):
        """
        x0 is the development point for the Carleman matrix for the slog
        u is the initial value such that slog(u)=0 or equivalently sexp(0)=u

        if no u is specified we have slog(x0)=0
        """

        bsym = b
        self.bsym = bsym
        self.N = N
        self.iprec = iprec
        x0sym = x0
        self.x0sym = x0sym

        self.prec = None


        bname = repr(bsym).strip('0').replace('.',',')
        if bsym == sqrt(2):
           bname = "sqrt2"
        if bsym == e**(1/e):
           bname = "eta"

        x0name = repr(x0sym)
        if x0name.find('.') > -1:
            if x0.is_real():
                x0name = repr(float(x0sym)).strip('0').replace('.',',')
            else:
                x0name = repr(complex(x0sym)).strip('0').replace('.',',')
        # by some reason save does not work with additional . inside the path

        self.path = "savings/itet_%s"%bname + "_N%04d"%N + "_iprec%05d"%iprec + "_a%s"%x0name

        if iprec != None:
            b = num(bsym,iprec)
            self.b = b
            x0 = num(x0sym,iprec)
            if x0.is_real():
                R = RealField(iprec)
            else:
                R = ComplexField(iprec)
            self.x0 = x0
        else:
            if b == e and x0 == 0:
                R = QQ
            else:
                R = SR
        self.R = R


	#Carleman matrix
        if x0 == 0:
            #C = Matrix([[ m**n*log(b)**n/factorial(n) for n in range(N)] for m in range(N)])
            coeffs = [ln(b)**n/factorial(n) for n in xrange(N)]
        else:
            #too slow
            #C = Matrix([ [ln(b)**n/factorial(n)*sum([binomial(m,k)*k**n*(b**x0)**k*(-x0)**(m-k) for k in range(m+1)]) for n in range(N)] for m in range(N)])

            coeffs = [b**x0-x0]+[b**x0*ln(b)**n/factorial(n) for n in xrange(1,N)]
        def psmul(A,B):
            N = len(B)
            return [sum([A[k]*B[n-k] for k in xrange(n+1)]) for n in xrange(N)]
        
        C = Matrix(R,N)

        row = vector(R,[1]+(N-1)*[0])
        C[0] = row
        for m in xrange(1,N):
            row = psmul(row,coeffs)
            C[m] = row
  
        A = (C - identity_matrix(N)).submatrix(1,0,N-1,N-1)
        self.A = A

        print "A computed."

        if iprec != None:
            A = num(A,iprec)

        row = A.solve_left(vector([1] + (N-2)*[0]))

        print "A solved."

        self.slog0coeffs = [0]+[row[n] for n in range(N-1)]
        self.slog0poly = PolynomialRing(R,'x')(self.slog0coeffs[:int(N)/2])
        
        slog0ps = FormalPowerSeriesRing(R)(self.slog0coeffs)
        sexp0ps = slog0ps.inv()
        #print self.slog0ps | self.sexp0ps
        self.sexp0coeffs = sexp0ps[:N]
        self.sexp0poly = PolynomialRing(R,'x')(self.sexp0coeffs[:int(N)/2])

        self.slog_raw0 = lambda z: self.slog0poly(z-self.x0)

        print "slog reversed."

        #the primary or the upper fixed point
        pfp = exp_fixpoint(b,1,prec=iprec)
        self.pfp = pfp

        r = abs(x0-pfp)

        #lower fixed point
        lfp = None
        if b <= R(e**(1/e)):
             lfp = exp_fixpoint(b,0,prec=iprec)
             r = min(r,abs(x0-lfp))
        self.lfp = lfp

        self.r = r


        self.c = 0
        if not u == None:
            self.c = - self.slog(u)

    def cmp_ir(self,z):
        """ 
        returns -1 for left, 0 for in, and 1 for right from initial region
        cut line is on the north ray from pfp.

        Works only for real x0.
        """
        pfp = self.pfp
        x0 = self.x0
        if x0 > 0.5:
            print z,abs(z)
            if real(z) >= real(pfp) and abs(z) < abs(pfp):
                return 0
            if real(z) < real(pfp):
                return -1
            if real(z) > real(pfp):
                return 1
        else:
            if imag(z) > imag(pfp):
                if real(z) > real(pfp):
                    return 1
                if real(z) < real(pfp):
                    return -1
            if real(z) < real(pfp) and real(z) > log(real(pfp)) + log(sqrt(1+tan(imag(z))**2)):
                return 0
            if real(z) > real(pfp):
                return 1
            if real(z) < real(pfp):
                return -1

    def slog2(self,z):
        """
        In the complex plane continued slog for base > eta
        """
        
        b = self.b
        z = num(z,self.iprec)

        n = 0
        while self.cmp_ir(z) == -1:
            z = b**z
            n += 1
 
        if n > 0:
            return self.c + self.slog_raw0(z) - n
          
        n = 0
        while self.cmp_ir(z) == +1:
            z = z.log(b)
            n+=1

        assert self.cmp_ir(z) == 0, self.cmp_ir(z)

        return self.c + self.slog_raw0(z) + n


    def slog1(self,z):
        """
        In the complex plane continued slog for base <= eta and x0 near attracting fixpoint
        """
        
        slog = self.slog1
        slog_raw = self.slog_raw
        b = self.b
        x0 = self.x0
        N = self.N
        z = num(z,self.iprec)
        r = self.r

        n = 0
        while abs(z-x0) > r/2:
            z = b**z
            n += 1

        return self.c + self.slog_raw0(z) - n

    def slog(self,z,debug=0):
        """
        slog continued into the complex plane where possible.
        Should always be possible if the real part of the development point
        is left from the lower fixed point
        """

        z = num(z,self.iprec)
        if z.is_real():
            res=self.slog_real(z,debug)
        elif self.lfp == None:
            #Only complex fixed points
            res=self.slog2(z)
        else:
            res=self.slog1(z)
   
        if self.prec == None: return res
        else: return num(res,self.prec)

    def slog_real(self,x,debug=0):
        """
        Development point is x0
        real continued slog
        """
        if self.iprec != None:
           x = num(x,self.iprec)

        b = self.b
        x0 = self.x0
        pfp = self.pfp
        lfp = self.lfp
        
        if lfp == None:
            direction = 1
        elif x < lfp and x0 < lfp:
            direction = 1
        elif pfp < x and pfp < x0:
            direction = 1
        elif lfp < x and x < pfp and lfp < x0 and x0 < pfp: 
            direction = -1
        else:
            print "x and x0 must be in the same segment of R divided by the lower and upper fixed point", "x:",x,"x0:",x0,"lfp:",lfp,"ufp",pfp
            return NaN

        n=0
        while direction*(x - x0) < 0:
            if debug>=2: print n,':','x:',x,'x0',x0,'dir',direction
            xp = x
            x = b**x
            n+=1

        if n>0:
            if abs(xp-x0) < abs(x-x0):
                n-=1
                x=xp
            if debug>=1: print 'x->b^x n:',n,'x:',x
            return self.c  + self.slog_raw0(x) - n

        while direction*(x - x0) > 0 and x>0:
            if debug>=2: print n,':','x:',x,'x0',x0,'dir',direction
            xp = x
            x = x.log(b)
            n+=1

        if n>0 and abs(xp-x0) < abs(x-x0):
            n-=1
            x=xp
            if debug>=1: print 'x->log_b(x) n:',n,'x:',x

        return self.c  + self.slog_raw0(x) + n

    def sexp_raw(self,x):
        x0 = self.x0
        c = self.c
        N = self.N
        a = self.sexp0coeffs

        return x0+sum([a[n]*(x-c)**n for n in range(1,int(N)/2)])

    def sexp(self,x):
        """
        Development point is x0-1
        """
        if isinstance(x,float) and self.iprec != None:
           x = RealField(self.iprec)(x)
            
        sexp = self.sexp
        sexp_raw = self.sexp_raw
        b = self.b
        c = self.c

        xt = x - c
        if real(xt)<-0.5:
            return log(sexp(x+1))/log(b)
        if real(xt)>0.5:
            return b**(sexp(x-1))
        return sexp_raw(x)

    def calc_prec(self):
        if self.prec != None:
            return self.prec
        iv0 = IntuitiveTetration(self.bsym,self.N-1,iprec=self.iprec,x0=self.x0sym)
        self.iv0 = iv0
        d = lambda x: self.slog(x) - iv0.slog(x)
        maximum = find_maximum_on_interval(d,0,1,maxfun=20)
        minimum = find_minimum_on_interval(d,0,1,maxfun=20)
        print "max:", maximum[0].n(20), 'at:', maximum[1]
        print "min:", minimum[0].n(20), 'at:', minimum[1]
        self.err = max( abs(maximum[0]), abs(minimum[0]))
        print "slog err:", self.err.n(20)
        self.prec = floor(-self.err.log(2))
        
        self.sexp_err = abs(iv0.sexp(0.5) - self.sexp(0.5))
        print "sexp err:", self.sexp_err.n(20)
        self.sexp_prec = floor(-log(self.sexp_err)/log(2.0))
        return self

    def backup(self):
        print "Writing to `" + self.path + ".sobj'."
        save(self,self.path)
        if self.prec != None: save(self.prec,self.path+"_prec"+repr(self.prec))
        return self
