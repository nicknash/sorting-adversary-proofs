#!/usr/bin/env python3
"""Directed-rounding certificate for the determinant constant K = 347/50.

The analytic proof reduces every near-central comparison to the scalar envelope
B(delta,r;a,b,lambda) in the accompanying paper.  This program verifies that a
fixed rational piecewise-linear schedule a(delta), b(delta), together with one
rational lambda witness on each interval box, satisfies

    B(delta,r;a(delta),b(delta),lambda) < log(347/50)

for 0 <= delta <= 411/1000 and 0 <= r <= 1.

Theorem-critical evaluation uses mpmath.iv interval arithmetic at 120 decimal
places.  Ordinary binary floating point is used only to *propose* a lambda;
the resulting integer / 10^12 witness is then checked by interval arithmetic
on the entire box.  All domain endpoints and schedule knots are rational.

As with any computer-assisted proof using a numerical library, rigor is
conditional on the correctness of the interval implementation.  The code is
written so that every final upper/lower-bound composition is itself performed
in interval arithmetic; no rounded scalar is silently treated as an exact
upper or lower bound.
"""
from __future__ import annotations

import math
from collections import deque
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 120
mp.iv.dps = 120
I = mp.iv.mpf

K = I(347) / I(50)
TARGET = mp.iv.log(K)
TARGET_LOWER = mp.mpf(TARGET._mpi_[0])
D0 = I(1) / mp.iv.sqrt(K - I(1))

# (1000*delta, 10^9*a(delta), 10^9*b(delta)).  Linear interpolation is used
# between consecutive knots.  Every entry is an exact integer.
RAW = [
    (0, 622454434, 622424669),
    (20, 619095674, 625535911),
    (40, 615380539, 628496630),
    (60, 611228294, 631313547),
    (80, 606581110, 633952170),
    (100, 601325567, 636408839),
    (120, 595325316, 638653695),
    (140, 588378953, 640666245),
    (160, 580204170, 642417260),
    (180, 570394627, 643880998),
    (200, 558360320, 645041599),
    (220, 543240708, 645950414),
    (240, 523955919, 647234041),
    (260, 503631525, 627425532),
    (280, 484458268, 576626027),
    (300, 465515284, 602315113),
    (320, 446808252, 631351002),
    (340, 428343050, 660180668),
    (360, 410125825, 707228286),
    (380, 392162933, 690669770),
    (400, 374460973, 732158061),
    (410, 365700000, 750000000),
    (411, 364823903, 751784194),
]


def IF(q: Fraction):
    """Exact rational converted to an enclosing interval."""
    return I(q.numerator) / I(q.denominator)


def lo(x):
    return mp.mpf(x._mpi_[0])


def hi(x):
    return mp.mpf(x._mpi_[1])


# ---------------------------------------------------------------------------
# Floating-point proposal stage.  These routines never certify anything.
# ---------------------------------------------------------------------------

def f_phip(x: float, d: float, a: float) -> float:
    tp = d + a
    return 2 * a * x**3 / (1 + tp * tp) + 3 * (a * x - math.log1p(a * x))


def f_phim(x: float, d: float, b: float) -> float:
    tm = b - d
    return -2 * b * x**3 / (1 + tm * tm) + 3 * (-b * x - math.log1p(-b * x))


def f_ratios(x: float, d: float, a: float, b: float):
    if abs(x) < 1e-14:
        return 1.5 * a * a, 1.5 * b * b
    return f_phip(x, d, a) / (x * x), f_phim(x, d, b) / (x * x)


def f_cross(length: float, P: float, N: float) -> float:
    """Closed form of the cross-over saving (proposal stage only)."""
    if P <= N:
        return 0.0
    if N < 1e-14:
        U = 1 + P * length
        return 0.5 * ((P * length + 1) * (1 - 1 / U) - math.log(U))
    s0 = (P - N) / (2 * P * N)
    L = min(length, s0)
    if L <= 0:
        return 0.0
    U = 1 + P * L
    V = 1 - N * L
    t1 = (P * length + 1) * (1 - 1 / U) - math.log(U)
    t2 = (N * length - 1) * (1 / V - 1) - math.log(V)
    J1 = ((P * length + 1) * math.log(U) - (U - 1)) / (P * P)
    J2 = (-(N * length - 1) * math.log(V) + (1 - V)) / (N * N)
    I3 = P / (P + N) * J1 + N / (P + N) * J2
    return max(0.0, 0.5 * (t1 + t2 - 2 * P * N * I3))


def f_corrs(a: float, b: float, r: float):
    P = math.sqrt(max(0.0, r))
    N = math.sqrt(max(0.0, 1.0 - r))
    if P >= N:
        cp = f_cross(a, P, N)
        cm = 0.25 * b * b * (P - N) ** 2
    else:
        cp = 0.25 * a * a * (N - P) ** 2
        cm = f_cross(b, N, P)
    return cp, cm


def f_eval(d: float, a: float, b: float, r: float, lam: float) -> float:
    P = math.sqrt(max(0.0, r))
    N = math.sqrt(max(0.0, 1.0 - r))
    lim = 1.5 * (lam * a * a + (1 - lam) * b * b)
    if r > 1e-15:
        rp, rm = f_ratios(P, d, a, b)
        pos = max(lim, lam * rp + (1 - lam) * rm)
    else:
        pos = 0.0
    if r < 1 - 1e-15:
        rp, rm = f_ratios(-N, d, a, b)
        neg = max(lim, lam * rp + (1 - lam) * rm)
    else:
        neg = 0.0
    cp, cm = f_corrs(a, b, r)
    base = (
        lam * math.log1p(1 / (d + a) ** 2)
        + (1 - lam) * math.log1p(1 / (b - d) ** 2)
    )
    return base + r * pos + (1 - r) * neg - lam * cp - (1 - lam) * cm


def f_best_lambda(d: float, a: float, b: float, r: float) -> float:
    """Find a candidate minimizer of the convex piecewise-linear lambda envelope."""
    P = math.sqrt(max(0.0, r))
    N = math.sqrt(max(0.0, 1.0 - r))
    lp = 1.5 * a * a
    lm = 1.5 * b * b
    candidates = [0.0, 1.0]
    for x, active in ((P, r > 1e-15), (-N, r < 1 - 1e-15)):
        if not active:
            continue
        rp, rm = f_ratios(x, d, a, b)
        den = (lp - lm) - (rp - rm)
        if abs(den) > 1e-14:
            lam = (rm - lm) / den
            if 0 < lam < 1:
                candidates.append(lam)
    return min((f_eval(d, a, b, r, lam), lam) for lam in candidates)[1]


# ---------------------------------------------------------------------------
# Certified interval stage.
# ---------------------------------------------------------------------------

def ratio_iv(x, d, a, b, lam):
    """R_lambda(x) at a fixed sign-endpoint x, with interval d,a,b."""
    tp = d + a
    tm = b - d
    rp = (
        I(2) * a * x / (I(1) + tp * tp)
        + I(3) * (a * x - mp.iv.log(I(1) + a * x)) / (x * x)
    )
    rm = (
        -I(2) * b * x / (I(1) + tm * tm)
        + I(3) * (-b * x - mp.iv.log(I(1) - b * x)) / (x * x)
    )
    return lam * rp + (I(1) - lam) * rm


def cross_lower(length_lower, rpoint: Fraction, positive_dominant: bool = True):
    """Certified lower bound for the cross-over saving Gamma.

    rpoint is chosen at the side of the r-box closest to 1/2.  Monotonicity of
    the integrand then makes this a lower bound throughout that box.  The
    supplied length is a certified lower bound for a or b.
    """
    rr = IF(rpoint)
    if positive_dominant:
        P = mp.iv.sqrt(rr)
        N = mp.iv.sqrt(I(1) - rr)
    else:
        P = mp.iv.sqrt(I(1) - rr)
        N = mp.iv.sqrt(rr)

    if rpoint == Fraction(1, 2):
        return mp.mpf("0")

    ell = I(length_lower)
    if hi(N) < mp.mpf("1e-100"):
        U = I(1) + P * ell
        val = I(1) / I(2) * (
            (P * ell + I(1)) * (I(1) - I(1) / U) - mp.iv.log(U)
        )
        return max(mp.mpf("0"), lo(val))

    s0 = (P - N) / (I(2) * P * N)
    # A point no larger than either the certified length or the true s0.
    L_lower = min(lo(ell), lo(s0))
    if L_lower <= 0:
        return mp.mpf("0")
    L = I(L_lower)

    U = I(1) + P * L
    V = I(1) - N * L
    t1 = (P * ell + I(1)) * (I(1) - I(1) / U) - mp.iv.log(U)
    t2 = (N * ell - I(1)) * (I(1) / V - I(1)) - mp.iv.log(V)
    J1 = ((P * ell + I(1)) * mp.iv.log(U) - (U - I(1))) / (P * P)
    J2 = (-(N * ell - I(1)) * mp.iv.log(V) + (I(1) - V)) / (N * N)
    I3 = P / (P + N) * J1 + N / (P + N) * J2
    val = I(1) / I(2) * (t1 + t2 - I(2) * P * N * I3)
    return max(mp.mpf("0"), lo(val))


def evaluate(si, dlo: Fraction, dhi: Fraction, rlo: Fraction, rhi: Fraction):
    """Return a certified upper bound for one delta-r box."""
    dmid = (dlo + dhi) / 2
    rmid = (rlo + rhi) / 2

    d0i, a0i, b0i = RAW[si]
    d1i, a1i, b1i = RAW[si + 1]

    dl = IF(dlo)
    dh = IF(dhi)
    d = dl + I([0, 1]) * (dh - dl)
    d0 = I(d0i) / I(1000)
    d1 = I(d1i) / I(1000)
    w = (d - d0) / (d1 - d0)
    a = I(a0i) / I(10**9) + w * I(a1i - a0i) / I(10**9)
    b = I(b0i) / I(10**9) + w * I(b1i - b0i) / I(10**9)

    # Floating point proposes lambda; exact integer / 10^12 is certified below.
    dmf = float(dmid)
    wmf = (dmf - d0i / 1000) / (d1i / 1000 - d0i / 1000)
    amf = a0i / 1e9 + wmf * (a1i - a0i) / 1e9
    bmf = b0i / 1e9 + wmf * (b1i - b0i) / 1e9
    lam_float = f_best_lambda(dmf, amf, bmf, float(rmid))
    lam_int = max(0, min(10**12, int(round(lam_float * 10**12))))
    lam = I(lam_int) / I(10**12)

    tp = d + a
    tm = b - d
    if (
        lo(a) <= 0
        or hi(a) >= 1
        or lo(b) <= 0
        or hi(b) >= 1
        or lo(tp) <= 0
        or lo(tm) <= 0
    ):
        raise AssertionError(("feasibility", si, dlo, dhi, a, b, tp, tm))

    base = (
        lam * mp.iv.log(I(1) + I(1) / (tp * tp))
        + (I(1) - lam) * mp.iv.log(I(1) + I(1) / (tm * tm))
    )
    base_upper = hi(base)

    R0 = I(3) / I(2) * (lam * a * a + (I(1) - lam) * b * b)
    R0_upper = hi(R0)

    # Convexity of R_lambda on each sign interval means that, over all
    # 0 <= P <= sqrt(rhi), it is enough to inspect x=0 and x=sqrt(rhi).
    if rhi > 0:
        x = mp.iv.sqrt(IF(rhi))
        pos_upper = max(R0_upper, hi(ratio_iv(x, d, a, b, lam)))
    else:
        pos_upper = mp.mpf("0")

    # Likewise the negative interval is contained in [-sqrt(1-rlo),0].
    if rlo < 1:
        y = mp.iv.sqrt(I(1) - IF(rlo))
        neg_upper = max(R0_upper, hi(ratio_iv(-y, d, a, b, lam)))
    else:
        neg_upper = mp.mpf("0")

    # r*pos + (1-r)*neg is affine in r once the two scalar upper bounds
    # have been fixed, so its maximum over the box is attained at an endpoint.
    mix0 = hi(IF(rlo) * I(pos_upper) + (I(1) - IF(rlo)) * I(neg_upper))
    mix1 = hi(IF(rhi) * I(pos_upper) + (I(1) - IF(rhi)) * I(neg_upper))
    mixture_upper = max(mix0, mix1)

    half = Fraction(1, 2)
    a_lower = lo(a)
    b_lower = lo(b)

    if rhi <= half:
        # N >= P: Gamma_+ >= a^2(N-P)^2/4.  The reflected Gamma_- is
        # the cross-over term and is smallest at r=rhi.
        gap = mp.iv.sqrt(I(1) - IF(rhi)) - mp.iv.sqrt(IF(rhi))
        cp = max(
            mp.mpf("0"),
            lo(I(a_lower) * I(a_lower) * gap * gap / I(4)),
        )
        cm = cross_lower(b_lower, rhi, positive_dominant=False)
    elif rlo >= half:
        # P >= N: Gamma_+ is cross-over; Gamma_- has the constant gap.
        cp = cross_lower(a_lower, rlo, positive_dominant=True)
        gap = mp.iv.sqrt(IF(rlo)) - mp.iv.sqrt(I(1) - IF(rlo))
        cm = max(
            mp.mpf("0"),
            lo(I(b_lower) * I(b_lower) * gap * gap / I(4)),
        )
    else:
        # A box straddling 1/2 can always discard the nonnegative savings.
        cp = cm = mp.mpf("0")

    correction_lower = lo(lam * I(cp) + (I(1) - lam) * I(cm))

    # Compose the final upper bound with interval operations as well.
    upper = hi(I(base_upper) + I(mixture_upper) - I(correction_lower))

    info = (
        float(dlo),
        float(dhi),
        float(rlo),
        float(rhi),
        lam_float,
        lam_int,
        base_upper,
        pos_upper,
        neg_upper,
        mixture_upper,
        cp,
        cm,
        correction_lower,
        upper,
    )
    return upper, info


D_SUB = 10
R_SUB = 100
STOP = Fraction(411, 1000)

queue = deque()
for si in range(len(RAW) - 1):
    d0 = Fraction(RAW[si][0], 1000)
    d1 = Fraction(RAW[si + 1][0], 1000)
    if d0 >= STOP:
        break
    d1 = min(d1, STOP)
    span = d1 - d0
    for j in range(D_SUB):
        x0 = d0 + span * j / D_SUB
        x1 = d0 + span * (j + 1) / D_SUB
        for k in range(R_SUB):
            queue.append(
                (si, x0, x1, Fraction(k, R_SUB), Fraction(k + 1, R_SUB), 0)
            )

max_upper = mp.mpf("-inf")
max_info = None
passed = 0
splits = 0
max_depth = 0

while queue:
    si, dlo, dhi, rlo, rhi, depth = queue.popleft()
    upper, info = evaluate(si, dlo, dhi, rlo, rhi)
    if upper < TARGET_LOWER:
        if upper > max_upper:
            max_upper = upper
            max_info = info
        passed += 1
        continue
    if depth >= 14:
        raise AssertionError(("maximum subdivision depth", depth, info, TARGET_LOWER))
    dmid = (dlo + dhi) / 2
    rmid = (rlo + rhi) / 2
    next_depth = depth + 1
    queue.extend(
        [
            (si, dlo, dmid, rlo, rmid, next_depth),
            (si, dlo, dmid, rmid, rhi, next_depth),
            (si, dmid, dhi, rlo, rmid, next_depth),
            (si, dmid, dhi, rmid, rhi, next_depth),
        ]
    )
    splits += 1
    max_depth = max(max_depth, next_depth)

if hi(D0) >= mp.mpf(STOP.numerator) / STOP.denominator:
    raise AssertionError(("near/large-offset cover gap", D0, STOP))

coefficient = I(2) / (mp.iv.log(K) / mp.iv.log(I(2)))

print("PASS")
print("K", K)
print("target", TARGET)
print("D0", D0, "cover", float(STOP))
print("cells", passed, "splits", splits, "depth", max_depth)
print("maxub", mp.nstr(max_upper, 70))
print("margin", mp.nstr(TARGET_LOWER - max_upper, 60))
print("coefficient", coefficient)
print("maxinfo", max_info)
