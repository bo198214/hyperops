#does not really belong to a powerseries package but there is currently no
#other place for it

from sage.rings.formal_powerseries import FormalPowerSeriesRing
def msexp(n,digits):
    #sexp(z)=exp^z(1)=exp^{z+1}(0)
    x=var('x')
    P = FormalPowerSeriesRing(QQ)
    sexp = P.Exp.it_matrixpower(x+1,n,RealField(digits))[0]
    return lambda z: sexp(x=z)


def it_matrixpower(p,t,n,root_field=RR):
    """
    t times Iteration via matrix power. t is a complex number.
    This method can also iterate power series with p[0]!=0.
    It is identical with the regular iteration for the case p[0]==0.
    However in the case p[0]!=0 it is no finite operation anymore and
    hence requires the size n of the Carleman matrix to use.
    This matrix which has the coefficients of p in its first row
    is raised to the t-th power and then the coefficients 
    of the first row are returned.

    Works currently only if the eigenvalues are all different.
    """
    assert n>=2, "Carleman matrix must at least be of size 2 to retrieve the coefficients. But given was " + repr(n)
    CM = p.carleman_matrix(n)
    ev = CM.charpoly().roots(root_field)
    assert len(ev) == n, "Carleman matrix must have exactly " + repr(n) + "eigenvalues, but has " + repr(len(ev))

    Char = [0]*n
    for k in range(n):
        #here is possibility for improvement of precision
        #to separate the fractional from the root parts
        #expanding the product
        Char[k] = CM - ev[k][0]*identity_matrix(n)

    #we want to have the first row of the product of the matrices
    #thatswhy we mulitply in front with:
    prod = vector(p.K,[0,1]+[0]*(n-2))
    prodwo = [0]*n
    for k in range(n):
        prodwo[k]=prod #these are the first terms until k-1

        #no need to continue
        if k == n-1:
            break

        #and we add the terms starting with k+1
        for i in range(k+1,n):
            prodwo[k] = prodwo[k] * Char[i]

        prod = prod * Char[k]

    sprodwo = [0]*n
    for k in range(n):
        if k==0:
            sprodwo[k] = ev[k][0] - ev[1][0]
            start = 2
        else:
            sprodwo[k] = ev[k][0] - ev[0][0]
            start = 1

        for i in range(start,n):
            if i != k:
                sprodwo[k] = sprodwo[k] * (ev[k][0] - ev[i][0])

    res = ev[0][0]**t/sprodwo[0] * prodwo[0]
    for k in range(1,n):
        res += ev[k][0]**t/sprodwo[k]*prodwo[k]

    return res.list()


def sexp(p,n,res_field=RR):
    """
    t times Iteration via matrix power. t is a complex number.
    This method can also iterate power series with p[0]!=0.
    It is identical with the regular iteration for the case p[0]==0.
    However in the case p[0]!=0 it is no finite operation anymore and
    hence requires the size n of the Carleman matrix to use.
    This matrix which has the coefficients of p in its first row
    is raised to the t-th power and then the coefficients 
    of the first row are returned.

    Works currently only if the eigenvalues are all different.
    """
    assert n>=2, "Carleman matrix must at least be of size 2 to retrieve the coefficients. But given was " + repr(n)
    CM = p.carleman_matrix(n)
    ev = [ r[0] for r in CM.charpoly().roots(QQbar) ]
    assert len(ev) == n, "Carleman matrix must have exactly " + repr(n) + "eigenvalues, but has " + repr(len(ev))

    #We want to compute:
    #sum over k: evk^t*(CM-ev1*I)*(CM-ev2*I)*. omit k * (CM-evn*I)/(evk-ev1)*.. omit k *(evk-evn)
    Char = [0]*n
    for k in range(n):
        #here is possibility for improvement of precision
        #to separate the fractional from the root parts
        #expanding the product
        Char[k] = CM - ev[k]*identity_matrix(n)

    #we want to have the first row of the product of the matrices
    #thatswhy we mulitply in front with:
    prod = vector(QQbar,[0,1]+[0]*(n-2))
    prodwo = [0]*n
    for k in range(n):
        prodwo[k]=prod #these are the first terms until k-1

        #no need to continue
        if k == n-1:
            break

        #and we add the terms starting with k+1
        for i in range(k+1,n):
            prodwo[k] = prodwo[k] * Char[i]

        prod = prod * Char[k]

    sprodwo = [0]*n
    for k in range(n):
        if k==0:
            sprodwo[k] = ev[k] - ev[1]
            start = 2
        else:
            sprodwo[k] = ev[k] - ev[0]
            start = 1

        for i in range(start,n):
            if i != k:
                sprodwo[k] = sprodwo[k] * (ev[k] - ev[i])

    for k in range(n):
        print ev[k]
        print prodwo[k][0]/sprodwo[k]
        print res_field
    #return lambda t: sum(res_field(ev[k])**t*res_field(prodwo[k][0]/sprodwo[k]) for k in range(n))
    return [ev,[prodwo[k][0]/sprodwo[k] for k in range(n)]]

def intuitive_abel_seq(p,n):
    """
    Returns the first n coefficients of the intuitive Abel power sequence,
    obtained from an nxn Carleman/Bell matrix.
    This method does not work for p[0]=0.
    """
    assert n>=2, "Carleman matrix must at least be of size 2 to retrieve the coefficients."
    B=p.carleman_matrix(n)-diagonal_matrix([1]*(n))
    x=B[range(1,n),range(n-1)].solve_left(matrix([[1] + [0]*(n-2)]))
    return [-1]+x[0].list()

def inv_schroeder_expb(fp):
    PP = PolynomialRing(QQ,'c')
    c = PP('c')  
    P = FPSRing(PP)
    f = P(lambda n: c**n/factorial(n)).dec().scalm(2)
    g = f.schroeder().inv()     

def sexpa(a,prec=167,N=64):
    """
    The super exponential via the inverse Schroeder function
    for an exponential b^x with fixed point a.
    """
    R = RealField(prec)
    P = FPSRing(R)
    a = R(a)
    b = R(a**(1/a))
    c = R(ln(a))
    F = P(lambda n: ln(b)**n/factorial(n)).dec().scalm(a)
    s = F.schroeder()
    si = s.inv()
    if c < 1:
        d = s.polynomial(N)(1-a)
    else:
        d = s.polynomial(N)(1)

    sip = si.polynomial(N)
    f = lambda x: a+sip(c**x * d)
    return f

def sexp_eta(prec=53,x0=0.5):
    """
    The superexponential to base e^(1/e)
    """
    R = RealField(prec)
    eta = R(e**(1/e))
    f = lambda x: eta**x
    fi = lambda x: log(x)/log(eta)
    def super(x,t,N=20):
        xn = x
        x0n = x0
        x0n1 = x0
        for n in range(N):
            xn = f(xn)
        for n in range(N):
            x0n = f(x0n)
        x0n1 = f(x0n)
        y = (x0n1-x0n)*t + xn
        for n in range(N):
            y = fi(y)
        return y
    return super
            
    
    
def symm(N,prec=167):
    R = RealField(prec)
    b = R(sqrt(2))
    fa = {}
    sym = {}
    x = 1
    y = b
    sym[x] = "1"
    sym[y] = "b"

    f = {}
    f[x] = y
    fa[x] = y 
    for k in range(N):
        fn = {}
        for x in f.keys():
            y = f[x]
            fn[-y]=-x
            fa[-y]=-x
            sym[-y]="-(" + sym[y] + ")"
            sym[-x]="-(" + sym[x] + ")"
            #print 's',-y,-x
            fn[x+1]=(b**y)
            fa[x+1]=(b**y)
            sym[x+1]="(" + sym[x] + ")+1"
            sym[b**y]="b**(" + sym[y] + ")"
            #print '1',x+1,b**y
        
        f = fn
        args = fa.keys()
        args.sort()
        xp = -2
        yp = -Infinity
        for x in args:
            y = fa[x]
            if n(y)<=n(yp):
                print k,':',(sym[xp],sym[yp]), (sym[x],sym[y])
                print k,(xp,yp),(x,y)
                break
            yp = y
            xp = x
    
    return line([[x,n(fa[x])] for x in args])

def laguerre_weights(N):
    v = PolynomialRing(QQ,'v').gen()
    p = laguerre(N,v)
    q = laguerre(N+1,v)
    x = []
    prec = 53
    while len(x) < N:
        x = p.roots(multiplicities=False,ring=RealField(prec))
        prec *= 2
    w = [x[i]*exp(x[i])/((N+1)*q(x[i]))**2 for i in range(0,N)]
    return (x,w)

def legendre_weights(N):
    v = PolynomialRing(QQ,'v').gen()
    p = legendre_P(N,v)
    prec = 53
    x = []
    while len(x) < N:
        x = p.roots(multiplicities=False,ring=RealField(prec))
        prec *= 2
    q = diff(p)
    w = [2/(1-x[i]**2)/q(x[i])**2 for i in range(N)]
    return (x,w)

def hermite_weights(M):
    v = PolynomialRing(QQ,'v').gen()
    N = 2*M - 1
    p = hermite(N,v)
    prec = 53
    x = []
    while len(x) < M:
        x = p.roots(multiplicities=False,ring=RealField(prec))[M-1:]
        prec *= 2
    q = hermite(N-1,v)
    c = 2**(N-1) * factorial(N)/ N**2 * n(sqrt(pi),prec) 
    w = [ exp(x[i]**2) * c / q(x[i])**2 for i in range(M) ]
    return (x,w)

def test_laguerre(lw):
    (x,w)=lw
    N = len(x)
    prec = x[0].prec()
    C = ComplexField(prec)
    f = exp
    s = 0
    for i in range(N):
        t = x[i]
        z = C(-1,t)
        s += w[i] * f(z)/z/(z-1)
        s += w[i] * (f(z)/z/(z-1)).conjugate()
        s /= C(0,2*pi)
    print s
    print exp(f(0.0))-f(.0) - s

def cauchy_super_odd(lw):
    (x,w)= lw
    M = len(x)
    prec = x[0].prec()
    C = ComplexField(prec)
    R = RealField(prec)
    fo = [ C(0.5) ] * M
    fo[0] = 1
    f = [0] * M
    f[0] = 1
    while True:
        for n in range(1,M):
            f[n] = w[0] * exp(1.0)/(1-C(0,x[n]))
            for k in range(1,M):
                z = C(0,x[n])
                it = C(0,x[k])
            
                y  = exp(fo[k]) / (+1+it-z)
                y -= log(fo[k]).conjugate() / (-1-it-z)
                y += exp(fo[k]).conjugate() / (+1-it-z)
                y -= log(fo[k]) / (-1+it-z)
                f[n] += w[k] * y
    
        print f[1]
        for i in range(M):
            fo[i] = f[i]

def cauchy_super_even(lw):
    (x,w)= lw
    M = len(x)
    prec = x[0].prec()
    C = ComplexField(prec)
    R = RealField(prec)
    fo = [ C(0.5) ] * M
    f = [0] * M
    while True:
        for n in range(M):
            f[n] = 0
            for k in range(M):
                z = C(0,x[n])
                it = C(0,x[k])
            
                y  = exp(fo[k]) / (+1+it-z)
                y -= log(fo[k]).conjugate() / (-1-it-z)
                y += exp(fo[k]).conjugate() / (+1-it-z)
                y -= log(fo[k]) / (-1+it-z)
                f[n] += w[k] * y
    
        print f[0]
        for i in range(M):
            fo[i] = f[i]

def cauchy_super_even_test(lw,F=exp):
    (x,w)= lw
    M = len(x)
    prec = x[0].prec()
    C = ComplexField(prec)
    R = RealField(prec)
    fo = [ F(C(0,x[i])) for i in range(M) ] 
    f = [0] * M
    for n in range(M):
        f[n] = 0
        for k in range(M):
            z = C(0,x[n])
            it = C(0,x[k])
        
            y  = F(+1+it) #/ (+1+it-z)
            y -= F(-1-it) #/ (-1-it-z)
            y += F(+1-it) #/ (+1-it-z)
            y -= F(-1+it) #/ (-1+it-z)
            print y
            f[n] += w[k] * y
    op = 20
    for k in range(M):
        print fo[k].n(op),f[k].n(op),(f[k] - fo[k]).n(op)
