"""Independent certificate checker: Python standard library, integer arithmetic only.
CSV rows: n, t*S, then n+1 descending root brackets (lo*S,hi*S).
The only analytic inputs are the lemmas in the paper's finite verification section.
"""
import csv
import sys
from pathlib import Path
from fractions import Fraction

S = 1 << 55

def require(ok, message):
    if not ok:
        raise ValueError(message)

def polynomial(n, t, y):
    # a_k = S**k U_k(y/S); p*S**(n+1) = a_(n+1)-2*t*a_n+t*t*a_(n-1)
    a, b = 1, 2*y
    for _ in range(1, n+1):
        c = 2*y*b - S*S*a
        if _ == n:
            return c - 2*t*b + t*t*a
        a, b = b, c
    raise AssertionError

def cdf(a, up):
    m = len(a)
    f = [S if x <= 0 else 0 for x in a]
    z = [None]*4
    for k in range(1, m):
        for i in range(m-k):
            l, h = a[i], a[i+k]
            if h <= 0:
                f[i] = S
            elif l >= 0:
                f[i] = 0
            else:
                d = h-l
                f[i] = ((-l)*f[i]+h*f[i+1]+(d-1 if up else 0))//d
        if k == m-3:
            z[0] = f[1]
        if k == m-2:
            z[1], z[2] = f[1], f[0]
        if k == m-1:
            z[3] = f[0]
    return z

def evaluate(n, t, brackets):
    require(len(brackets)==2*(n+1), 'wrong number of brackets')
    a, b = [t-S], [t-S]
    for l, h in zip(brackets[::2], brackets[1::2]):
        require(-S < l < h < S, 'root outside interval')
        require(polynomial(n,t,l)*polynomial(n,t,h)<0, 'no sign change')
        require(t-h>b[-1], 'overlapping root intervals')
        a.append(t-h); b.append(t-l)
    require(t+S>b[-1], 'last root outside interval')
    a.append(t+S); b.append(t+S)
    lo = [S-2*f for f in cdf(a, True)]
    hi = [S-2*f for f in cdf(b, False)]
    require(all(x<=y for x,y in zip(lo,hi)), 'inverted CDF bounds')
    return lo,hi

def lower2(n,a,b):
    return a[0][1]+a[0][2]+n*(a[0][3]-b[1][0])

def main(path):
    nprev = 2; tprev = None; prev = None; count = 0; margins=[]; origins=[]
    with open(path,newline='') as f:
        for row in csv.reader(f):
            n,t,*brackets=map(int,row)
            require(3<=n<=19 and 0<t<=S//2,'unexpected n or t')
            cur=evaluate(n,t,brackets)
            if n!=nprev:
                require(n==nprev+1 and (tprev is None or tprev==S//2),'missing order or interval')
                require(t==S//(1<<24),'wrong start')
                M=6*(n+1)*(n+3)*(n+4); L=lower2(n,cur,cur)
                require(L*S>4*M*t*t,'origin not certified')
                origins.append(Fraction(L,2*t)-Fraction(2*M*t,S))
            else:
                require(tprev<t,'nonincreasing partition')
                L=lower2(n,prev,cur)
                require(L>0,'interval not certified')
                margins.append(Fraction(L,2*tprev));count+=1
            nprev,tprev,prev=n,t,cur
    require(nprev==19 and tprev==S//2,'incomplete certificate')
    print(f'PASS n=3..19: {count} intervals, {len(origins)} origin neighborhoods')
    print('Minimum normalized interval lower bound:', float(min(margins)))
    print('Minimum origin margin:', float(min(origins)))
if __name__=='__main__':
    main(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('brackets.csv'))
