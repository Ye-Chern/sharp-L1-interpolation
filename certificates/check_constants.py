"""Exact rational checks of the small numerical constants in Section 6.
The integral bounds use decreasing-function left rectangles and a power-law tail.
No floating-point values enter any comparison.
"""
from fractions import Fraction as F
from math import isqrt

def require(ok):
    if not ok:
        raise ValueError('constant bound failed')

def atan_bounds(q, terms):
    s=sum(((-1)**k*q**(2*k+1)/ (2*k+1) for k in range(terms)),F(0))
    nxt=(-1)**terms*q**(2*terms+1)/(2*terms+1)
    return min(s,s+nxt),max(s,s+nxt)

# Machin's identity pi=16 atan(1/5)-4 atan(1/239).
a,b=atan_bounds(F(1,5),12);c,d=atan_bounds(F(1,239),5)
pi_lo,pi_hi=F(314159,100000),F(314160,100000)
require(pi_lo<16*a-4*d and 16*b-4*c<pi_hi)
sqrt24_lo,sqrt24_hi=F(489897,100000),F(489898,100000)
require(sqrt24_lo**2<24<sqrt24_hi**2)
require(7*pi_hi*24*sqrt24_hi/512<F(5051,1000))
require(F(22,21)*63*sqrt24_hi/512<F(632,1000))

def J_upper(L):
    h=F(1,1000); B=F(12); N=int((B-L)/h)
    require(L+N*h==B)
    S=10**12; total=0
    for k in range(N):
        x=L+k*h
        w=(1+x*x/24)**-6
        total+=(w.numerator*S+w.denominator-1)//w.denominator
    # W(x) <= 24^6/x^12 for x>=12.
    return F(total,S)*h+F(24**6,11*12**11)
J1,J2=J_upper(F(57,20)),J_upper(F(57,10))
require(J1<F(153,1000) and J2<F(6,1000))
z=F(24,25); poly=z-z**3/3+z**5/10-z**7/42
require(poly>0 and (2*poly)**2>F(822,1000)**2*pi_hi)
require(F(57,20)*F(11,10)<pi_lo)
G=F(822,1000)-2/pi_lo*(F(654,1000)*F(5051,1000)/20+F(11,20)*F(159,1000))
D=F(5051,1000)/(20*pi_lo)*(3+3*F(11,10)*F(31,20))
require(G>F(661,1000) and D<F(653,1000))
print('PASS: all numerical bounds in Section 6')
print('J(2.85) upper:',float(J1),'J(5.7) upper:',float(J2))
print('G/r lower:',float(G),'|Delta|/r upper:',float(D))
