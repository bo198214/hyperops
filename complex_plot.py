import sys

from sage.plot.contour_plot import contour_plot
from sage.plot.line import line
from sage.plot.graphics import Graphics
from sage.plot.plot import multi_graphics, parametric_plot
from sage.symbolic.constants import pi
from sage.functions.other import arg, real, imag, floor, ceil, sqrt
from sage.functions.log import log, exp
from sage.functions.trig import acos
from sage.rings.integer import Integer
from sage.rings.real_mpfr import RR, RealField
from sage.rings.complex_mpfr import ComplexField
from sage.misc.functional import n as numeric

CC = ComplexField()


def pair_from_complex(f):
    """
    Given a complex function f it creates a pair of functions (g,h)
    such that g(x)=real(f(x)) and h(x)=imag(f(x))
    """
    return lambda z: real(f(z)), lambda z: imag(f(z))


pfc = pair_from_complex


def complex_contour_plot(f, *args, **kwargs):
    a = contour_plot(lambda x,y: real(f(CC(x,y))), *args, **kwargs)
    b = contour_plot(lambda x,y: imag(f(CC(x,y))), *args, **kwargs)
    return a + b


def complex_parametric_plot(f, interval, coarseness=0.005, max_dist_ratio=50, **kwargs):
    (a, b) = interval

    IDiv = 10

    points_from = []
    points_to = []
    order = {}
    length_ = 0
    points_from.append(a)
    points_to.append(f(a))

    xmax=sys.float_info.min
    ymax=sys.float_info.min
    xmin=sys.float_info.max
    ymin=sys.float_info.max
    for i in range(1, IDiv + 1):
        t = a + i * (b - a) / IDiv
        points_from.append(t)
        z = f(t)
        if real(z) < xmin:
            xmin = real(z)
        if real(z) > xmax:
            xmax = real(z)
        if imag(z) < ymin:
            ymin = imag(z)
        if imag(z) > ymax:
            ymax = imag(z)
        points_to.append(z)
        order[i-1] = i
        length_ += abs(points_to[i] - points_to[i-1])


    # if 'xmax' in kwargs:
    #     xmax = kwargs['xmax']
    # else:
    #     kwargs['xmax'] = xmax
    # if 'ymax' in kwargs:
    #     ymax = kwargs['ymax']
    # else:
    #     kwargs['ymax'] = ymax
    # if 'xmin' in kwargs:
    #     xmin = kwargs['xmim']
    # else:
    #     kwargs['xmin'] = xmin
    # if 'ymin' in kwargs:
    #     ymin = kwargs['ymin']
    # else:
    #     kwargs['ymin'] = ymin
    xwidth = xmax-xmin
    ywidth = ymax-ymin
    diag = sqrt(xwidth**2+ywidth**2)
    print(xwidth,ywidth,diag)
    ends = []

    def iterating1():
        i1 = 0
        yield i1
        while i1 in order:
            i2 = order[i1]
            yield i2
            i1 = i2

    def iterating2():
        i1 = 0
        while i1 in order:
            i2 = order[i1]
            yield i1,i2
            i1 = i2

    def iterating3():
        i1 = 0
        while i1 in order:
            i2 = order[i1]
            if i2 not in order:
                break
            i3 = order[i2]
            yield i1,i2,i3
            i1 = i2

    def insert_point(i1,i2):
        nonlocal xmin, xmax, ymin, ymax
        t3 = (points_from[i1]+points_from[i2])/2
        n = len(points_from)
        points_from.append(t3)
        z = f(t3)
        points_to.append(z)
        if real(z) < xmin:
            xmin = real(z)
        if real(z) > xmax:
            xmax = real(z)
        if imag(z) < ymin:
            ymin = imag(z)
        if imag(z) > ymax:
            ymax = imag(z)
        order[i1] = n
        order[n] = i2
        return n

    def make_smooth(i1, i2, i3):
        d1 = points_to[i2] - points_to[i1]
        d2 = points_to[i3] - points_to[i2]
        l1 = abs(d1)
        l2 = abs(d2)
        if l1/l2 > max_dist_ratio:
            ends.append(i1)
            return
        if l2/l1 > max_dist_ratio:
            ends.append(i2)
            return

        phi = acos((real(d1)*real(d2)+imag(d1)*imag(d2))/(l1*l2))

        arc1 = l1/diag*phi
        arc2 = l2/diag*phi

        is_coarse = False
        i4 = i1
        if arc1 > coarseness:
            i4 = insert_point(i1, i2)
            make_smooth(i1,i4,i2)
            is_coarse = True
        i5 = i3
        if arc2 > coarseness:
            i5 = insert_point(i2, i3)
            make_smooth(i2, i5, i3)
            is_coarse = True
        if is_coarse:
            make_smooth(i4,i2,i5)

    for i1, i2, i3 in list(iterating3()):
        make_smooth(i1, i2, i3)

    p = Graphics()
    a = []
    for k in iterating1():
        a.append((float(real(points_to[k])), float(imag(points_to[k]))))
        if k in ends or k not in order:
            p += line(a, **kwargs)
            a = []
    return p


# Skaleneinteilung
# 1. mindestens 2 fette (Vielfache von 10er-Potenzen) Striche
# 2. Abstand der Unterstriche soll eindl. Dezimalbruch sein
# 3. Niemals mehr als 10 Striche
# 2.&3. => moegliche Unterstrich-Abstaende: 1/2, 1/4, 1/5
# 4. Niemals weniger als 6 Striche
# [0..1): *0.0,*0.1,*0.2,...,*0.9 = 10
# [0..1]: *0,0.2,0.4,0.6,0.8,*1 = 6
# [0..2): *0,0.2,0.4,0.6,0.8,*1,1.2,...,1.8 = 10
# [0..2]: *0,0.25,0.5,0.75,*1,...,*2 = 9
# [0..2.5): *0,0.25,...,2.5 = 10
# [0..2.5]: *0,0.5,*1,1.5,*2,2.5 = 6
# [0..5): *0,0.5,...,4.5 = 10
# [0..5]: *0,*1,*2,*3,*4,*5 = 6
# [0..10): *0,...,*9 = 10
def scale_ticks(a, b, equal=10, is_open=False, nsubticks=None, dd=None):
    """
    in each direction:
    * At least 1 major tick (multiples of power of 10) in (a,b)
    * At least 5 ticks and at most 10 ticks
    dd specifies the distance between subticks, should get values of the form 10**m/n
    nsubticks specifies the number of subticks between 2 major ticks.
    open specifies whether the interval should be assumed to be open or closed.
    """
    diff = b - a
    digits = floor(log(diff, 10))

    s = 10.0 ** digits
    K = ceil(a / s)

    #     if (K+1)*s > b:
    #        digits -= 1
    #        s /= 10
    #        K = ceil(a/s)

    subticks = []
    if equal:
        for n in range(equal):
            subticks.append(a + n * (b - a) / equal)
        subticks.append(b)
        return subticks
    if nsubticks is None and dd is None:
        # count the number 10**(digits-1) steps in (a,b)
        s = 10 ** (digits - 1)
        # step after a
        if is_open:
            sa = floor(a / s + 1)
        else:
            sa = ceil(a / s)
        # step before b
        if is_open:
            sb = ceil(b / s - 1)
        else:
            sb = floor(b / s)
        sdiff = sb - sa  # step difference
        if sdiff < 10:
            d = 1
        elif sdiff < 20:
            d = 10 / 5
        elif sdiff < 25:
            d = 10 / 4
        elif sdiff < 50:
            d = 10 / 2
        elif sdiff < 200:
            d = 10
        else:
            assert False, sdiff

        da = ceil(Integer(sa) / d) * d
        db = floor(Integer(sb) / d) * d

        # print s,sa,sb,d,da,db
        k = da
        if k != a:
            subticks.append(a)
        while k <= db:
            t = s * k
            subticks.append(t)
            k += d
        if k != b:
            subticks.append(a)

    elif nsubticks is not None:
        # nsubticks are given
        d = s / nsubticks
        t = K * s
        m = 0

        while is_open and t < b or not is_open and t <= b:
            if not is_open or is_open and t > a:
                if m % nsubticks == 0:
                    major_ticks.append(t)
                else:
                    subticks.append(t)
                m += 1
                t += d

        t = K * s - d
        while is_open and t > a or not is_open and t >= a:
            subticks.append(t)
            t -= d
    elif dd is not None:
        k = K
        while k * s <= b:
            t = k * s
            if not is_open or is_open and t > a:
                major_ticks.append(t)
            t += dd
            while t < (k + 1) * s and is_open and t < b or not is_open and t <= b:
                subticks.append(t)
                t += dd
            k += 1

        t = K * s - dd
        while is_open and t > a or not is_open and t >= a:
            subticks.append(t)
            t -= dd

    return subticks


# def conformal_plot(f,xrange=(-1,1),yrange=(-1,1),xticks=10,yticks=10,**kwargs):
#     """
#     images of lines with constant real part are blue
#     images of lines with constant imag part are orange
#     the first and last values of each range are plotted
#     xticks>=2 is the number of blue lines
#     yticks>=2 is the number of red lines
#     """

#     (xa,xb)=xrange
#     (ya,yb)=yrange
#     xdiff = xb-xa
#     ydiff = yb-ya


#     xd = 10**(-xdigits)
#     if isinstance(xdiff,int) or isinstance(xdiff,Integer):
#         xdiff = RR(xdiff)
#     if isinstance(ydiff,int) or isinstance(ydiff,Integer):
#         ydiff = RR(ydiff)

#     dx = xdiff/(xticks-1)
#     dy = ydiff/(yticks-1)

#     return conformal_dplot(f,xrange,yrange,dx=dx,dy=dy,**kwargs)

def conformal_polar_plot(f, z0, R, rticks=10, aticks=12, upperHalf=True, asr1=True, **kwargs):
    """
    Conformal polar plot.
    Powerseries have a development point a convergence radius.
    images of lines with constant radius are green
    images of lines with constant angle are red
    the image of the line with radius R will be drawn
    rticks>=1 is the number of green lines
    aticks>=1 is the number of red lines
    """

    if isinstance(z0, int) or isinstance(z0, Integer):
        z0 = CC(z0)
    if isinstance(R, int) or isinstance(R, Integer):
        R = RealField(z0.prec())(R)

    if upperHalf:
        pir = RR(pi)
    else:
        pir = RR(2 * pi)
        aticks *= 2

    p = Graphics()

    dr = R / rticks
    r = dr
    while r <= R + dr / 2:
        p = p + complex_parametric_plot(lambda t: f(z0 + r * exp(CC(0, t))), (0, pir), rgbcolor='green', **kwargs)
        r += dr

    da = pir / aticks
    if upperHalf:
        a = da
    else:
        a = 0

    while a < pir - da / 2:
        p = p + complex_parametric_plot(lambda t: f(z0 + t * exp(CC(0, a))), (0, R), rgbcolor='red', **kwargs)
        a += da

    if asr1:
        p.set_aspect_ratio(1)
    return p


def conformal_ring_plot(f, z0, rmin, R, rticks=10, aticks=12, upperHalf=True, asr1=True, **kwargs):
    """
    Conformal polar plot.
    Powerseries have a development point a convergence radius.
    images of lines with constant radius are green
    images of lines with constant angle are red
    the image of the line with radius R will be drawn
    rticks>=1 is the number of green lines
    aticks>=1 is the number of red lines
    """

    if isinstance(z0, int) or isinstance(z0, Integer):
        z0 = CC(z0)
    if isinstance(R, int) or isinstance(R, Integer):
        R = RealField(z0.prec())(R)

    if upperHalf:
        pir = RR(pi)
    else:
        pir = RR(2 * pi)
        aticks *= 2

    p = Graphics()

    dr = (R - rmin) / rticks
    r = rmin
    while r <= R + dr / 2:
        p = p + complex_parametric_plot(lambda t: f(z0 + r * exp(CC(0, t))), (0, pir), rgbcolor='green', **kwargs)
        r += dr

    da = pir / aticks
    if upperHalf:
        a = 0
    else:
        a = 0

    p = p + complex_parametric_plot(lambda t: f(z0 + t * exp(CC(0, a))), (rmin, R), rgbcolor='black', **kwargs)
    a += da
    while a < pir - da / 2:
        p = p + complex_parametric_plot(lambda t: f(z0 + t * exp(CC(0, a))), (rmin, R), rgbcolor='red', **kwargs)
        a += da

    if asr1:
        p.set_aspect_ratio(1)
    return p


def conformal_disk_plot(f, z0, R, upperHalf=True, asr1=True, nsubticks=None, dd=None, **kwargs):
    """
    Conformal disk plot.
    Powerseries have a development point a convergence radius.
    images of lines with constant imaginary part are blue
    images of lines with constant real part are orange
    the image of the line with radius R will be drawn
    xticks>=2 is the number of green lines
    yticks>=2 is the number of red lines
    """

    if isinstance(z0, int) or isinstance(z0, Integer):
        z0 = CC(z0)
    if isinstance(R, int) or isinstance(R, Integer):
        R = RealField(z0.prec())(R)

    x0 = real(z0)
    y0 = imag(z0)
    (xbticks, xnticks) = scale_ticks(x0 - R, x0 + R, is_open=True, nsubticks=nsubticks, dd=dd)
    if upperHalf:
        ya = y0
    else:
        ya = y0 - R
    (ybticks, ynticks) = scale_ticks(ya, y0 + R, is_open=True, nsubticks=nsubticks, dd=dd)

    if upperHalf:
        te = RR(pi)
    else:
        te = RR(2 * pi)

    p = complex_parametric_plot(lambda t: f(z0 + R * exp(CC(0, t))), (0, te), rgbcolor='black')
    if asr1:
        p.set_aspect_ratio(1)

    for x in xbticks:
        xd = x - x0
        yd = sqrt(R ** 2 - xd ** 2)
        p = p + complex_parametric_plot(lambda t: f(CC(x, t)), (ya, y0 + yd), rgbcolor='orange', thickness=1, **kwargs)

    for x in xnticks:
        xd = x - x0
        yd = sqrt(R ** 2 - xd ** 2)
        p = p + complex_parametric_plot(lambda t: f(CC(x, t)), (ya, y0 + yd), rgbcolor='orange', thickness=0.5,
                                        **kwargs)

    for y in ybticks:
        yd = y - y0
        xd = sqrt(R ** 2 - yd ** 2)
        p = p + complex_parametric_plot(lambda t: f(CC(t, y)), (x0 - xd, x0 + xd), rgbcolor='blue', thickness=1,
                                        **kwargs)
    for y in ynticks:
        yd = y - y0
        xd = sqrt(R ** 2 - yd ** 2)
        p = p + complex_parametric_plot(lambda t: f(CC(t, y)), (x0 - xd, x0 + xd), rgbcolor='blue', thickness=0.5,
                                        **kwargs)

    if asr1:
        p.set_aspect_ratio(1)

    return p


def conformal_plot1(f, xrange=(-1, 1), yrange=(-1, 1), dd=None, nsubticks=None, asr1=True, **kwargs):
    (xa, xb) = xrange
    xticks = scale_ticks(xa, xb, is_open=False, dd=dd, nsubticks=nsubticks)
    (ya, yb) = yrange
    yticks = scale_ticks(ya, yb, is_open=False, dd=dd, nsubticks=nsubticks)
    p = conformal_plot_grid(f, xticks, yticks, **kwargs)
    if asr1:
        p.set_aspect_ratio(1)
    return p


def conformal_plot_grid0(f, xticks, yticks, **kwargs):
    p = Graphics()
    xa = min(xticks)
    xb = max(xticks)
    ya = min(yticks)
    yb = max(yticks)
    xrange = (xa, xb)
    yrange = (ya, yb)
    for x in xticks:
        if x == xa:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 1
        elif x == xb:
            kwargs["linestyle"] = "--"
            kwargs["thickness"] = 1
        else:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 0.5
        p += complex_parametric_plot(lambda t: f(CC(x, t)), yrange, rgbcolor='orange', **kwargs)

    for y in yticks:
        if y == ya:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 1
        elif y == yb:
            kwargs["linestyle"] = "--"
            kwargs["thickness"] = 1
        else:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 0.5
        p += complex_parametric_plot(lambda t: f(CC(t, y)), xrange, rgbcolor='blue', **kwargs)
    return p


def conformal_plot_grid(f, xticks, yticks, **kwargs):
    p = Graphics()
    xa = min(xticks)
    xb = max(xticks)
    ya = min(yticks)
    yb = max(yticks)
    xrange = (xa, xb)
    yrange = (ya, yb)
    for x in xticks:
        if x == xa:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 1
        elif x == xb:
            kwargs["linestyle"] = "--"
            kwargs["thickness"] = 1
        else:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 0.5
        p += parametric_plot(pair_from_complex(lambda t: f(CC(x, t))), yrange, rgbcolor='orange', **kwargs)

    for y in yticks:
        if y == ya:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 1
        elif y == yb:
            kwargs["linestyle"] = "--"
            kwargs["thickness"] = 1
        else:
            kwargs["linestyle"] = "-"
            kwargs["thickness"] = 0.5
        p += parametric_plot(pair_from_complex(lambda t: f(CC(t, y))), xrange, rgbcolor='blue', **kwargs)
    return p


def conformal_plot2(f, xrange=(-1, 1), yrange=(-1, 1), dd=None, nsubticks=None, asr1=True, **kwargs):
    (xa, xb) = xrange
    xticks = scale_ticks(xa, xb, is_open=False, dd=dd, nsubticks=nsubticks)
    (ya, yb) = yrange
    yticks = scale_ticks(ya, yb, is_open=False, dd=dd, nsubticks=nsubticks)

    p1 = conformal_plot_grid(lambda z: z, xticks, yticks)
    p2 = conformal_plot_grid(f, xticks, yticks, **kwargs)
    p1.set_aspect_ratio("auto")
    if asr1:
        p2.set_aspect_ratio(1)

    p = multi_graphics([(p1, (0, 0.25, 0.5, 0.5)), (p2, (0.5, 0, 1, 1))])
    return p
