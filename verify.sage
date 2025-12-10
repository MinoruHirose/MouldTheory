"""
This is a program intended to be run on SageMath. For example, you can paste it into SageMathCell (https://sagecell.sagemath.org/) and execute it.
"""

from functools import lru_cache
from dataclasses import dataclass
from typing import Any

MAX_DEPTH = 3

def lift_to_fs(v):
    return FormalSum([(1,v)])

class Mould:
    def __init__(self, func):
        self.func = func
        pass

    #使わない
    def log(self):
        assert self([])==1
        ret = zero_mould
        u = I_mould
        for h in (1..MAX_DEPTH):
            u *= self - I_mould
            ret = ret + ((-1)^(h-1)) / h * u
        return ret

    def __call__(self, us):
        return self.func(us)

    def __mul__(self, other):
        def f(us):
            if type(other)==Integer or type(other)==Rational:
                return self(us)*other
            n = len(us)
            assert n>=0
            ret = 0
            for i in (0..n):
                j = n-i
                ret += self(us[:i]) * other(us[i:])
            return ret
        return Mould(func = f)

    def __rmul__(self, other):
        def f(us):
            n = len(us)
            assert n>=0

            if type(other)==Integer or type(other)==Rational:
                return self(us)*other
            assert False
        return Mould(func = f)

    def __add__(self, other):
        def f(us):
            return self(us)+other(us)
        return Mould(f)

    def __sub__(self, other):
        def f(us):
            return self(us) - other(us)
        return Mould(f)

    def invmul(self):
        assert self([])==1
        ret = I_mould
        for _ in (1..MAX_DEPTH):
            rem = I_mould - ret*self
            ret += rem
        return ret

    def invgari(self):
        assert self([])==1
        ret = I_mould
        for _ in (1..MAX_DEPTH):
            rem = I_mould - gari(ret,self)
            ret += rem
        return ret

zero_mould = Mould(lambda us:0)
I_mould = Mould(lambda us:1 if len(us)==0 else 0)

def flexion_up_left(us,us2):
    # us2 ⌈ us
    val = sum(u for u in us2)
    return [ u + (val if ind == 0 else 0) for ind,u in enumerate(us)]

def flexion_up_right(us,us2):
    # us ⌉ us2
    val = sum(u for u in us2)
    return [ u + (val if ind == len(us)-1 else 0) for ind,u in enumerate(us)]

def flexion_down_left(us,us2):
    # us2 ⌊ us
    # Bimouldではなく、u成分のみを考えているので単にusを返す
    return us

def flexion_down_right(us,us2):
    # us ⌋ us2
    # Bimouldではなく、u成分のみを考えているので単にusを返す
    return us

def arit(B,A):
    assert type(A)==Mould and type(B)==Mould
    def f(us):
        r = len(us)
        if r==0 or r==1:
            return 0
        ret = 0
        for i in (0..r):
            for j in (i..r):
                a1 = us[:i]
                a2 = us[i:j]
                a3 = us[j:]
                if len(a2)!=0 and len(a3)!=0:
                    ret += A(a1 + flexion_up_left(a3,a2)) * B(flexion_down_right(a2,a3))
                if len(a1)!=0 and len(a2)!=0:
                    ret -= A(flexion_up_right(a1,a2)+a3) * B(flexion_down_left(a2,a1))
        return ret
    return Mould(f)

def ari(A,B):
    return arit(B,A) - arit(A,B) + A*B - B*A

def preari(A,B):
    return arit(B,A) + A*B

def expari(A):
    assert A([])==0
    ret = I_mould
    U = I_mould
    for k in (1..MAX_DEPTH):
        U = preari(U,A)
        ret = ret + U * (1/factorial(k))
    return ret

def logari(A):
    assert A([])==1
    ret = zero_mould
    for _ in (1..MAX_DEPTH):
        rem = A - expari(ret)
        ret = ret + rem
    return ret

def get_pal():
    def f(us):
        if len(us)==0:
            return 1
        if len(us)==1:
            u1=us[0]
            return -1/2/u1
        if len(us)==2:
            u1,u2 = us
            return (u1+2*u2)/12/u1/u2/(u1+u2)
        if len(us)==3:
            u1,u2,u3 = us
            return -1/24/u1/(u1+u2)/u3
        assert False

    return Mould(f)

def get_paj():
    def f(us):
        return mul( 1/sum(us[:i]) for i in (1..len(us)) )
    return Mould(f)

def all_splits_for_gari(seq):
    seq = tuple(seq)
    ret = []
    for i1 in (0..len(seq)):
        for i2 in (i1+1..len(seq)):
            for i3 in (i2..len(seq)):
                alpha = seq[:i1]
                beta = seq[i1:i2]
                gamma = seq[i2:i3]
                if i3==len(seq):
                    ret.append((alpha,beta,gamma))
                else:
                    for new_split in all_splits_for_gari(seq[i3:]):
                        if len(gamma)+len(new_split[0])>0:
                            ret.append((alpha,beta,gamma)+new_split)
    return ret

def garit(B,A):
    Binv = B.invmul()
    def f(us):
        if len(us)==0:
            return A([])
        ret = 0
        for split in all_splits_for_gari(us):
            seq1 = []
            u = 1
            for j in range(len(split)):
                if j%3==0:
                    u *= B(flexion_down_right(split[j], split[j+1]))
                if j%3==1:
                    seq1 += flexion_up_right(flexion_up_left(split[j], split[j-1]), split[j+1])
                if j%3==2:
                    u *= Binv(flexion_down_left(split[j], split[j-1]))
            ret += u * A(seq1)
        return ret
    return Mould(f)

def gari(A,B,*CS):
    ret = garit(B,A)*B
    if len(CS)==0:
        return ret
    else:
        for C in CS:
            ret = gari(ret,C)
        return ret

# Adariの定義は2種類ある。
def Adari(A):
    inv_A = A.invgari()
    def func(B):
        return gari(preari(A,B), inv_A)

    # def func(B):
    #     return logari(gari(A,expari(B),A.invgari()))
    return func

# adgariの定義だが使わない
def adgari(A):
    inv_A = A.invgari()
    def func(B):
        return gari(gari(A,B), inv_A)

    # def func(B):
    #     return logari(gari(A,expari(B),A.invgari()))
    return func

def neg(M):
    def f(us):
        return M([-u for u in us])
    return Mould(f)

def sang(M):
    paj = get_paj()
    p1 = paj.invmul() * M * paj
    p2 = neg(Adari(paj)(p1) )
    return (p1+p2) * (1/2)

def leng(r):
    def func(M):
        return Mould(lambda us: (M(us) if len(us)==r else 0))
    return func

def slang(r):
    pal = get_pal()
    pal_inv = pal.invgari()
    def func(M):
        return Adari(pal)( leng(r)( Adari(pal_inv)( sang(M) ) ) )
    return func

def get_Brown_s():
    def f(us):
        if len(us)==0:
            return 0
        if len(us)==1:
            x1 = us[0]
            return 1/2*(1/x1)
        if len(us)==2:
            x1 = us[0]
            x2 = us[0]+us[1]
            return (1/12)*( 1/x1/x2 + 1/x2/(x1-x2) )
        if len(us)>=3:
            return 0
    return Mould(f)

def get_Brown_xi(S):
    bs = get_Brown_s()
    return S + ari(S, bs) + 1/2*ari(ari(S, bs), bs)

@dataclass(frozen=True)
class Svalue:
    u: Any
    def __init__(self, u):
        if str(u)[0]=="-1":
            u = -u
        object.__setattr__(self, "u", u)
    def __str__(self):
        return f"S({self.u})"

def verify_Thm():
    PR = PolynomialRing(QQ, "u1,u2,u3,S_1,S_2,S_3,S_12,S_23,S_123")
    u1,u2,u3,S_1,S_2,S_3,S_12,S_23,S_123 = PR.gens()

    def fS(us):
        if len(us)!=1:
            return 0
        u = us[0]
        if str(u)[0]=="-":
            u = -u
        if u==u1:
            return S_1
        if u==u2:
            return S_2
        if u==u3:
            return S_3
        if u==u1+u2:
            return S_12
        if u==u2+u3:
            return S_23
        if u==u1+u2+u3:
            return S_123

        print(f"{u=}")
        assert False, u

    S = Mould(fS)
    Brown_S = get_Brown_xi(S)
    Ecalle_S = slang(1)(S)



    for depth in (0..3):
        us = [u1,u2,u3][:depth]
        left = Brown_S(us)
        right = Ecalle_S(us)

        print(f"The following is a result for depth {depth}")
        print()
        print(f"Brown's ξ(S):")
        print(f"{left}")
        print()
        print(f"Ecalle's slang_1(S):")
        print(f"{right}")
        print()
        print(f"The difference:")
        print(f"{left-right}")
        print()
        assert left==right
        print(f"Depth {depth} part is ok")
        print()
        print()


verify_Thm()
print("Finish")
