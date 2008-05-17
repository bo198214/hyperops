class PowerSeries:
    def __init__(self,p=[0,1]):
        self.memo = {}
        self.powmemo = {}
        if isinstance(p,list):
            def f(n):
                if n<len(p):
                    return p[n]
                else:
                    return 0
            self.f = f
        else:
            self.f = p


    def __call__(self,n):
        if not self.memo.has_key(n):
            self.memo[n] = self.f(n)
        return self.memo[n]
        
    def __add__(a,b):
        def ret(n):
            return a(n)+b(n)
        return PowerSeries(ret)

    def __sub__(a,b):
        def ret(n):
            return a(n)-b(n)
        return PowerSeries(ret)

    def __mul__(a,b):
        def ret(n):
            return sum(a(k)*b(n-k) for k in range(n))
        return PowerSeries(ret)

    def __div__(a,b):
        return a*reciprocal(b)

    def __pow__(a,n):
        res = prod(a for k in range(n))
        if not a.powmemo.has_key(n):
            a.powmemo[n] = res
        return a.powmemo[n]

    def reciprocal(a):
        #TODO
        return a

    def compose(a,b):
        #TODO
        return a

    def inverse(a):
        #TODO
        return a
    
    #static methods
    def Exp(self):
        def ret(n):
            return 1/factorial(n)
        #efficiency
        return compose(self,PowerSeries(ret))
        
