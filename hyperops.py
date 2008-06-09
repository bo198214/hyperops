"""
Title: HyperSage - a Sage library for tetration and hyper operations.
Creator: Andrew Robbins
Contributor: Jay D. Fox
Date: 2008-04-25
Description:

    hyperops/hyper.py contains functions that implement the common forms
    of hyper operations, including right/mother (implemented now),
    left, balanced, mixed, grandmother (includes zeration), daughter, 
    associative, exponential, and others.
    
"""

from sage.all import *
from special_functions import LambertW

def hyper_HC_simple(b, h, rank=3):
    """
    hyper_HC_simple(base, height, rank)

    This function is only defined for heights between 0, 1.
    For tetration, this is linear when height is between -1, 0 
    and exponential when the height is between 0, 1.
    """
    return b**h
    
def hyper_HD_simple(b, h, rank=3):
    """
    hyper_HD_simple(base, height, rank)
    
    This function is only defined for ranks between 2, 3.
    For many bases, this will make a smooth curve between
    multiplication (rank=2) and exponentiation (rank=3).
    """
    if rank == 2:
        return b*h
    elif rank == 3:
        return b**h
    else:
        return (b*h)*cos(rank*pi/2)**2 + (b**h)*sin(rank*pi/2)**2

def hyper(rank):
    def ret(base, height, 
        hc=[0, hyper_HC_simple, hyperlog_HC_simple], 
        hd=[2, hyper_HD_simple, hyperlog_HD_simple]):
        if hd[0] <= rank and rank <= (hd[0] + 1):
            return hd[1](base, height, rank)
        elif rank < hd[0]:
            h = hyperlog(rank + 1)(base, height, hc, hd) + 1
            return hyper(rank + 1)(base, h, hc, hd)
        elif (hd[0] + 1) < rank:
            if hc[0] <= height and height <= (hc[0] + 1):
                return hc[1](base, height, rank)
            elif height < hc[0]:
                z = hyper(rank)(base, height + 1, hc, hd)
                return hyperlog(rank - 1)(base, z, hc, hd)
            elif (hc[0] + 1) < height:
                h = hyper(rank)(base, height - 1, hc, hd)
                return hyper(rank - 1)(base, h, hc, hd)
            else:
                return function('hyper' + str(rank), base, height)
        else:
            raise ValueError, "cannot compare rank, is it a number?"
    return ret

def hyperlog_HC_simple(b, z, rank=3):
    return log(z, b)
    
def hyperlog_HD_simple(b, z, rank=3):
    if rank == 2:
        return z/b
    elif rank == 3:
        return log(z)/log(b)
    else:
        # yes, this is actually the inverse of 'hyper_HD_simple'
        rp = rank*pi
        lb = log(b)
        head = QQ(2)*z/(b+b*cos(rp))
        tail = (LambertW(b**(QQ(2)*z/head-1)*tan(rp/2)**2*lb)/lb)
        return head - tail

def hyperlog(rank):
    def ret(base, inver, 
        hc=[0, hyper_HC_simple, hyperlog_HC_simple], 
        hd=[2, hyper_HD_simple, hyperlog_HD_simple]):
        if hd[0] <= rank and rank <= (hd[0] + 1):
            return hd[2](base, inver, rank)
        elif rank < hd[0]:
            h = hyperlog(rank + 1)(base, inver, hc, hd) - 1
            return hyper(rank + 1)(base, h, hc, hd)
        elif (hd[0] + 1) < rank:
            c0 = hyper(rank)(base, hc[0])
            if c0 <= inver and inver <= (c0 + 1):
                return hc[2](base, inver, rank)
            elif inver < c0:
                z = hyper(rank - 1)(base, inver, hc, hd)
                return hyperlog(rank)(base, z, hc, hd) - 1
            elif (c0 + 1) < inver:
                z = hyperlog(rank - 1)(base, inver, hc, hd)
                return hyperlog(rank)(base, z, hc, hd) + 1
            else:
                return function('hyper' + str(rank) + 'log', base, inver)
        else:
            raise ValueError, "cannot compare rank, is it a number?"
    return ret
    
def hyperroot(rank):
    def ret(inver, height):
        if height == 0:
            return NaN
        elif height == 1:
            return inver
        else:
            return function('hyper' + str(rank) + 'root', inver, height)
    return ret

tetrate = hyper(4)
superlog = hyperlog(4)
superroot = hyperroot(4)

pentate = hyper(5)
pentalog = hyperlog(5)
pentaroot = hyperroot(5)
