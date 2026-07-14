#!/usr/bin/env python3
"""Readable, self-contained numerical verifier for the Erdős 1038 proof.

The nine source sections below are a literal, human-readable consolidation of
the seven certificates run by the original master driver and their two local
utility modules.  Their local project imports have been removed; the loader
injects the same dependencies from the in-memory sections in this file.

Every logical certificate runs in a fresh subprocess, preserving the original
isolation of mpmath, Arb, and SciPy state.  Every unresolved interval sign,
failed assertion, exception, or nonzero child return code makes the suite fail.

Required third-party packages: mpmath, python-flint, and scipy.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import types


CERTIFICATES = (
    "verify_tao_sup_inequalities.py",
    "verify_onecut_global.py",
    "verify_low_k_mean_deficit_repair.py",
    "verify_negative_platform_affine_reference_basics.py",
    "verify_negative_platform_affine_uniform.py",
    "verify_negative_platform_terminal_refined_scalar.py",
    "verify_negative_platform_terminal_scalar.py",
)

# alias -> embedded filename.  These replace the local imports from the
# original separate-file implementation.
DEPENDENCY_ALIASES = {
    "negative_platform_fourier.py": {
        "core": "verify_mixed_interval_derivative_signs.py",
    },
    "verify_negative_platform_affine_uniform.py": {
        "core": "verify_mixed_interval_derivative_signs.py",
        "diagnostic": "negative_platform_fourier.py",
    },
    "verify_negative_platform_terminal_refined_scalar.py": {
        "core": "verify_mixed_interval_derivative_signs.py",
        "onecut": "verify_onecut_global.py",
    },
    "verify_negative_platform_terminal_scalar.py": {
        "onecut": "verify_onecut_global.py",
    },
}

SOURCES: dict[str, str] = {}


# ============================================================================
# EMBEDDED SOURCE: verify_mixed_interval_derivative_signs.py
# ============================================================================
SOURCES["verify_mixed_interval_derivative_signs.py"] = r'''#!/usr/bin/env python3
"""Outward Fourier machinery for the terminal mixed-interval derivatives.

This verifier uses Arb balls, geometric tails for the two Poisson weights,
and explicit 1/n Fourier tails.  Adaptive domain subdivision is performed in
the one-cut parameter q, interval width d, and location y, where

    left=(pi-d)y,  right=left+d.

Small-width endpoint charts are handled separately below.  A PASS is printed
only after every box has either a strictly directed derivative sign or has
entered one of those analytically bounded charts.
"""

from __future__ import annotations

from dataclasses import dataclass
import heapq
import math

import mpmath as mp
from flint import arb, acb, ctx
from scipy.optimize import brentq


ctx.prec = 160
mp.mp.dps = 70

Q_LO = mp.mpf("0.0106")
Q_HI = mp.mpf("0.0562908174574974221234199598975662836311517793")
PI = mp.pi
QSTAR_LO = mp.mpf("0.02571553686652745032257637166291965344")
QSTAR_HI = mp.mpf("0.02571553686652745032257637166491965344")


def B(lo, hi=None):
    lo = mp.mpf(lo)
    hi = lo if hi is None else mp.mpf(hi)
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    guard = mp.mpf("1e-65") * (1 + abs(mid) + abs(rad))
    return arb(f"{mp.nstr(mid, 80)} +/- {mp.nstr(rad + guard, 80)}")


def lo(x: arb) -> mp.mpf:
    value = x.lower()
    body = str(value).strip().strip("[]")
    if "+/-" in body:
        center, radius = (mp.mpf(part.strip()) for part in body.split("+/-"))
        return center - 2 * abs(radius) - mp.mpf("1e-65") * (1 + abs(center))
    center = mp.mpf(body)
    return center - mp.mpf("1e-65") * (1 + abs(center))


def hi(x: arb) -> mp.mpf:
    value = x.upper()
    body = str(value).strip().strip("[]")
    if "+/-" in body:
        center, radius = (mp.mpf(part.strip()) for part in body.split("+/-"))
        return center + 2 * abs(radius) + mp.mpf("1e-65") * (1 + abs(center))
    center = mp.mpf(body)
    return center + mp.mpf("1e-65") * (1 + abs(center))


def symmetric_error(radius) -> arb:
    radius = max(mp.mpf(0), mp.mpf(radius))
    return arb(0, arb(mp.nstr(radius, 80)))


def bisect(f, a, b, steps=180):
    fa, fb = f(a), f(b)
    assert fa * fb < 0
    for _ in range(steps):
        m = (a + b) / 2
        fm = f(m)
        if fa * fm <= 0:
            b, fb = m, fm
        else:
            a, fa = m, fm
    return (a + b) / 2


_crossing_cache = {}


def point_crossings(q):
    cache_key = mp.nstr(q, 60)
    if cache_key in _crossing_cache:
        return _crossing_cache[cache_key]
    H = 2 * q / (1 + q) ** 2
    A = mp.log(H) / mp.log(q)
    T = -mp.log(q)

    def fp(y):
        u = mp.exp(y)
        return mp.log(u) / A - mp.log((u - q) / (1 - q * u))

    def fm(y):
        u = mp.exp(y)
        return mp.log(u) / A - mp.log((u - q) / (q * u - 1))

    # A fast double-precision scan only supplies starting brackets.  The
    # returned roots are recomputed at high precision and then independently
    # certified by Arb sign brackets in family_box.
    qf = float(q)
    Hf = 2 * qf / (1 + qf) ** 2
    Af = math.log(Hf) / math.log(qf)
    Tf = -math.log(qf)

    def fpf(y):
        u = math.exp(y)
        return math.log(u) / Af - math.log((u - qf) / (1 - qf * u))

    def fmf(y):
        u = math.exp(y)
        return math.log(u) / Af - math.log((u - qf) / (qf * u - 1))

    grid = [1e-9 + (Tf - 2e-9) * j / 160 for j in range(161)]
    brackets = [(grid[j], grid[j + 1]) for j in range(160)
                if fpf(grid[j]) * fpf(grid[j + 1]) < 0]
    ypf = brentq(fpf, *brackets[-1])
    grid = [Tf + 1e-9 + 15 * j / 240 for j in range(241)]
    brackets = [(grid[j], grid[j + 1]) for j in range(240)
                if fmf(grid[j]) * fmf(grid[j + 1]) < 0]
    ymf = brentq(fmf, *brackets[0])
    yp = mp.findroot(fp, (mp.mpf(ypf - 1e-5), mp.mpf(ypf + 1e-5)))
    ym = mp.findroot(fm, (mp.mpf(ymf - 1e-5), mp.mpf(ymf + 1e-5)))
    out = mp.exp(yp), mp.exp(ym)
    _crossing_cache[cache_key] = out
    return out


@dataclass
class Family:
    q: arb
    H: arb
    ek: arb
    lam: arb
    rp: arb
    rm: arb
    logscale: arb


_family_cache = {}


@dataclass
class Dual:
    value: arb
    derivative: arb

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Dual) else Dual(x if isinstance(x, arb) else arb(x), arb(0))

    def __add__(self, other):
        other = self.coerce(other)
        return Dual(self.value + other.value, self.derivative + other.derivative)

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.value, -self.derivative)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Dual(self.value * other.value,
                    self.derivative * other.value + self.value * other.derivative)

    __rmul__ = __mul__

    def reciprocal(self):
        return Dual(1 / self.value, -self.derivative / self.value**2)

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()

    def __pow__(self, n):
        assert n == 2
        return self * self

    def log(self):
        return Dual(self.value.log(), self.derivative / self.value)


@dataclass
class AD2:
    value: object
    gradient: tuple

    @staticmethod
    def coerce(x):
        return x if isinstance(x, AD2) else AD2(x, (arb(0), arb(0)))

    def __add__(self, other):
        other = self.coerce(other)
        return AD2(self.value + other.value,
                   tuple(self.gradient[j] + other.gradient[j] for j in range(2)))

    __radd__ = __add__

    def __neg__(self):
        return AD2(-self.value, tuple(-z for z in self.gradient))

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return AD2(self.value * other.value,
                   tuple(self.gradient[j] * other.value
                         + self.value * other.gradient[j] for j in range(2)))

    __rmul__ = __mul__

    def reciprocal(self):
        return AD2(1 / self.value,
                   tuple(-z / self.value**2 for z in self.gradient))

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()

    def __pow__(self, n):
        if n == 2:
            return self * self
        raise NotImplementedError(n)

    def sin(self):
        return AD2(self.value.sin(), tuple(self.value.cos() * z for z in self.gradient))

    def cos(self):
        return AD2(self.value.cos(), tuple(-self.value.sin() * z for z in self.gradient))

    def log(self):
        return AD2(self.value.log(), tuple(z / self.value for z in self.gradient))


def family_box(qlo, qhi) -> Family:
    key = (mp.nstr(qlo, 40), mp.nstr(qhi, 40))
    if key in _family_cache:
        return _family_cache[key]

    # Both crossing branches decrease with q on the certified one-cut range.
    up_hi, um_hi = point_crossings(qlo)
    up_lo, um_lo = point_crossings(qhi)
    pad = mp.mpf("1e-38")
    qb = B(qlo, qhi)
    up = B(up_lo - pad, up_hi + pad)
    um = B(um_lo - pad, um_hi + pad)
    H_broad = 2 * qb / (1 + qb) ** 2
    A_broad = H_broad.log() / qb.log()

    # Certify the endpoint roots and monotonicity of both implicit branches.
    def equations(qarg, uparg, minus=False):
        HH = 2 * qarg / (1 + qarg) ** 2
        AA = HH.log() / qarg.log()
        den = qarg * uparg - 1 if minus else 1 - qarg * uparg
        return uparg.log() / AA - ((uparg - qarg) / den).log()

    for qpoint, upr, umr in ((qlo, up_hi, um_hi), (qhi, up_lo, um_lo)):
        qq = B(qpoint)
        assert lo(equations(qq, B(upr - pad))) > 0
        assert hi(equations(qq, B(upr + pad))) < 0
        assert hi(equations(qq, B(umr - pad), True)) < 0
        assert lo(equations(qq, B(umr + pad), True)) > 0

    qdual = Dual(qb, arb(1))
    updual = Dual(up, arb(1))
    umdual = Dual(um, arb(1))
    fp_q = equations(qdual, Dual(up, arb(0))).derivative
    fp_u = equations(Dual(qb, arb(0)), updual).derivative
    fm_q = equations(qdual, Dual(um, arb(0)), True).derivative
    fm_u = equations(Dual(qb, arb(0)), umdual, True).derivative
    assert hi(fp_q) < 0 and hi(fp_u) < 0
    assert lo(fm_q) > 0 and lo(fm_u) > 0

    def derived(qarg, uparg, umarg):
        HH = 2 * qarg / (1 + qarg) ** 2
        AA = HH.log() / qarg.log()
        BB = 1 - AA
        kk = AA / BB
        rawp = 1 - AA * (1 / qarg - qarg) / (
            qarg + 1 / qarg - uparg - 1 / uparg
        )
        rawm = 1 - AA * (1 / qarg - qarg) / (
            qarg + 1 / qarg - umarg - 1 / umarg
        )
        spp = BB * HH * (uparg - 1 / uparg) / (-rawp)
        smm = BB * HH * (umarg - 1 / umarg) / rawm
        rpp, rmm = 1 / uparg, 1 / umarg
        eta00 = 1 - 2 * kk * qarg / (1 - qarg)
        apii = kk + 1 - kk * (1 - qarg) / (1 + qarg)
        bpii = (4 * smm * rmm / (1 - rmm**2)
                + 4 * spp * rpp / (1 - rpp**2))
        ekk = kk / apii
        # xi is a convex mixture of two source shapes normalized to one at
        # pi.  This retains the exact cancellation lambda+(1-lambda)=1.
        lamp = (spp / bpii) * 4 * rpp / (1 - rpp**2)
        return HH, ekk, lamp, rpp, rmm, (apii * bpii).log()

    # Tight mean-value enclosures preserve the q/u branch correlation.  The
    # broad implicit boxes above supply rigorous u' bounds.
    up_slope = -fp_q / fp_u
    um_slope = -fm_q / fm_u
    qd = Dual(qb, arb(1))
    upd = Dual(up, up_slope)
    umd = Dual(um, um_slope)
    broad_derived = derived(qd, upd, umd)

    qmid = (qlo + qhi) / 2
    upmid, ummid = point_crossings(qmid)
    center_derived = derived(B(qmid), B(upmid - pad, upmid + pad),
                             B(ummid - pad, ummid + pad))
    qrad = (qhi - qlo) / 2

    def mean_value_ball(center, derivative):
        slope = max(abs(lo(derivative)), abs(hi(derivative)))
        return B(lo(center) - slope * qrad, hi(center) + slope * qrad)

    tight = [mean_value_ball(c, z.derivative)
             for c, z in zip(center_derived, broad_derived)]
    H, ek, lam, rp, rm, logscale = tight
    assert lo(ek) > 0 and lo(lam) > 0 and hi(lam) < 1
    out = Family(qb, H, ek, lam, rp, rm, logscale)
    _family_cache[key] = out
    return out


def poisson(rho, theta):
    return (1 - rho * rho) / (1 - 2 * rho * theta.cos() + rho * rho)


def densities(fam: Family, theta):
    ppi = (1 - fam.q) / (1 + fam.q)
    a = 1 - fam.ek * (poisson(fam.q, theta) - ppi)
    # Stable form of P_rho(0)-P_rho(theta).
    one_minus_cos = 2 * (theta / 2).sin() ** 2

    def pdiff(rho):
        den = 1 - 2 * rho * theta.cos() + rho * rho
        return 2 * rho * (1 + rho) * one_minus_cos / ((1 - rho) * den)

    gm = pdiff(fam.rm) * (1 - fam.rm**2) / (4 * fam.rm)
    gp = pdiff(fam.rp) * (1 - fam.rp**2) / (4 * fam.rp)
    b = (1 - fam.lam) * gm + fam.lam * gp
    return a, b


def normalized_coefficients(fam, M):
    ppi = (1 - fam.q) / (1 + fam.q)
    invapi = 1 - fam.ek * (1 - ppi)
    e0 = 1 - fam.ek * ((1 + fam.q) / (1 - fam.q) - ppi)
    Dm = 4 * fam.rm / (1 - fam.rm**2)
    Dp = 4 * fam.rp / (1 - fam.rp**2)
    eta = [None] + [fam.ek * fam.q**m for m in range(1, M + 1)]
    xi = [None] + [
        (1 - fam.lam) * fam.rm**m / Dm + fam.lam * fam.rp**m / Dp
        for m in range(1, M + 1)
    ]
    return invapi, e0, eta, xi, Dm, Dp


def interval_I(j, left, right):
    if j == 0:
        return right - left
    return ((j * right).sin() - (j * left).sin()) / j


def fourier_data(fam: Family, left, right, N=160, M=18):
    width = right - left
    Is = [interval_I(j, left, right) for j in range(N + M + 1)]

    invapi, e0, eta_coeff, xi_coeff, Dm, Dp = normalized_coefficients(fam, M)

    # Stable mass representations.
    qmass = e0 * Is[0]
    rmass = arb(0)
    for m in range(1, M + 1):
        gap = Is[0] - Is[m]
        qmass += 2 * eta_coeff[m] * gap
        rmass += 2 * xi_coeff[m] * gap

    eta_tail_coeff = fam.ek * fam.q ** (M + 1) / (1 - fam.q)
    xi_tail_coeff = ((1 - fam.lam) * fam.rm ** (M + 1) / ((1 - fam.rm) * Dm)
                     + fam.lam * fam.rp ** (M + 1) / ((1 - fam.rp) * Dp))
    mass_eta_err = 4 * hi(width) * hi(eta_tail_coeff) / mp.pi
    mass_xi_err = 4 * hi(width) * hi(xi_tail_coeff) / mp.pi
    qmass = qmass / arb.pi() + symmetric_error(mass_eta_err)
    rmass = rmass / arb.pi() + symmetric_error(mass_xi_err)

    X, Y = [], []
    moment_eta_err = mass_eta_err
    moment_xi_err = mass_xi_err
    for n in range(1, N + 1):
        yn = invapi * Is[n]
        xn = arb(0)
        # In the c0-2 sum c_m cos(m theta) representation, eta c0=1 and
        # xi c0=2 sum c_m.
        xi_c0 = 2 * ((1 - fam.lam) * fam.rm / ((1 - fam.rm) * Dm)
                     + fam.lam * fam.rp / ((1 - fam.rp) * Dp))
        xn += xi_c0 * Is[n]
        for m in range(1, M + 1):
            pair = Is[abs(n - m)] + Is[n + m]
            yn -= eta_coeff[m] * pair
            xn -= xi_coeff[m] * pair
        Y.append(yn / arb.pi() + symmetric_error(moment_eta_err))
        X.append(xn / arb.pi() + symmetric_error(moment_xi_err))
    return qmass, rmass, X, Y


def fourier_data_raw(fam: Family, left, right, N=160, M=18):
    """Same moments without tails; supports AD2 endpoint variables."""
    Is = [interval_I(j, left, right) for j in range(N + M + 1)]
    invapi, e0, eta_coeff, xi_coeff, Dm, Dp = normalized_coefficients(fam, M)
    qmass = e0 * Is[0]
    rmass = AD2.coerce(0) if isinstance(left, AD2) else arb(0)
    for m in range(1, M + 1):
        gap = Is[0] - Is[m]
        qmass += 2 * eta_coeff[m] * gap
        rmass += 2 * xi_coeff[m] * gap
    qmass /= arb.pi()
    rmass /= arb.pi()

    xi_c0 = 2 * ((1 - fam.lam) * fam.rm / ((1 - fam.rm) * Dm)
                 + fam.lam * fam.rp / ((1 - fam.rp) * Dp))
    X, Y = [], []
    for n in range(1, N + 1):
        yn = invapi * Is[n]
        xn = xi_c0 * Is[n]
        for m in range(1, M + 1):
            pair = Is[abs(n - m)] + Is[n + m]
            yn -= eta_coeff[m] * pair
            xn -= xi_coeff[m] * pair
        Y.append(yn / arb.pi())
        X.append(xn / arb.pi())
    return qmass, rmass, X, Y


def upper_derivative_raw(fam: Family, left, right, N=160, M=18):
    qmass, rmass, X, Y = fourier_data_raw(fam, left, right, N, M)
    at, bt = densities(fam, right)
    logH = fam.H.log()
    energy = logH * qmass * rmass
    peta = logH * qmass
    pxi = logH * rmass
    for n, (xn, yn) in enumerate(zip(X, Y), 1):
        energy -= 2 * xn * yn / n
        ct = (n * right).cos()
        peta -= 2 * ct * yn / n
        pxi -= 2 * ct * xn / n
    avg = energy / (qmass * rmass)
    return (at / (arb.pi() * qmass) * (pxi / rmass - avg - 1)
            + bt / (arb.pi() * rmass) * (peta / qmass - avg - 1))


def mixed_margin_raw(fam: Family, left, right, N=160, M=18):
    qmass, rmass, X, Y = fourier_data_raw(fam, left, right, N, M)
    energy = fam.H.log() * qmass * rmass
    for n, (xn, yn) in enumerate(zip(X, Y), 1):
        energy -= 2 * xn * yn / n
    return energy / (qmass * rmass) - (qmass * rmass / 2).log() - fam.logscale


def right_margin_box(qlo, qhi, dlo, dhi, Ncenter=800, Njet=20, M=24):
    """Outward direct F box for J=[pi-d,pi]."""
    if dlo <= 0:
        return None
    fam = family_box(qlo, qhi)
    dc = (dlo + dhi) / 2
    leftc, rightc = arb.pi() - B(dc), arb.pi()
    center = mixed_margin_raw(fam, leftc, rightc, Ncenter, M)
    qmass, rmass, _, _ = fourier_data(fam, leftc, rightc, N=0, M=M)
    _, _ = densities(fam, rightc)
    qmin, rmin = lo(qmass), lo(rmass)
    if qmin <= 0 or rmin <= 0:
        return None
    # Normalized outer energy tail; endpoint-normalized densities are <=1.
    center += symmetric_error(4 / (mp.pi**2 * Ncenter**2 * qmin * rmin))

    d = AD2(B(dlo, dhi), (arb(1), arb(0)))
    jet = mixed_margin_raw(fam, arb.pi() - d, AD2(arb.pi(), (arb(0), arb(0))),
                           Njet, M)
    if not jet.gradient[0].is_finite():
        return None
    variation = max(abs(lo(jet.gradient[0])), abs(hi(jet.gradient[0]))) \
        * (dhi - dlo) / 2
    # Derivative of the omitted boundary-subtracted tail.
    variation += 30 / (Njet * dlo) * (dhi - dlo) / 2
    return center + symmetric_error(variation + mp.mpf("1e-10"))


def certify_candidate_small_right(d0=mp.mpf(".05")):
    """Directed perturbation certificate for J=[pi-d,pi], 0<=d<=d0."""
    fam = family_box(QSTAR_LO, QSTAR_HI)

    def p2(r):
        return 2 * r * (1 - r) / (1 + r)**3

    def s4(r):
        return r * (1 + 11*r + 11*r*r + r**3) / (1 - r)**5

    Dm = 4 * fam.rm / (1 - fam.rm**2)
    Dp = 4 * fam.rp / (1 - fam.rp**2)
    alpha = -fam.ek * p2(fam.q) / 2
    beta = -((1 - fam.lam) * p2(fam.rm) / Dm
             + fam.lam * p2(fam.rp) / Dp) / 2
    M4a = fam.ek * s4(fam.q) / 12
    M4b = ((1 - fam.lam) * s4(fam.rm) / Dm
           + fam.lam * s4(fam.rp) / Dp) / 12
    Ca = max(abs(lo(alpha)), abs(hi(alpha))) + hi(M4a) * d0**2
    Cb = max(abs(lo(beta)), abs(hi(beta))) + hi(M4b) * d0**2
    ma, mb = 1 - Ca*d0**2, 1 - Cb*d0**2
    assert ma > 0 and mb > 0
    ea, eb = 2*Ca*d0**2/ma, 2*Cb*d0**2/mb
    perturb = 3*(ea + eb + ea*eb)
    perturb += Ca*d0**2/ma + Cb*d0**2/mb
    perturb += 5*d0**2 / (24*(1 - d0**2/mp.pi**2))
    edge = (-3 + 2*arb(2).log()
            + (2*arb.pi()**2 * fam.H).log() - fam.logscale)
    lower = lo(edge) - perturb
    assert lower > mp.mpf(".69")
    return lower


def certify_candidate_right_face(d0=mp.mpf(".05"), max_depth=14):
    small_lower = certify_candidate_small_right(d0)
    stack = [(d0, PI, 0)]
    evaluations = 0
    while stack:
        dlo, dhi, depth = stack.pop()
        value = right_margin_box(QSTAR_LO, QSTAR_HI, dlo, dhi)
        evaluations += 1
        if value is not None and lo(value) > 0:
            continue
        if depth >= max_depth:
            return False, (dlo, dhi, value, evaluations, small_lower)
        mid = (dlo + dhi) / 2
        stack.extend(((dlo, mid, depth + 1), (mid, dhi, depth + 1)))
    return True, (evaluations, small_lower)


def candidate_edge_density_constants(L0):
    fam = family_box(QSTAR_LO, QSTAR_HI)

    def p2(r): return 2*r*(1-r)/(1+r)**3
    def s4(r): return r*(1+11*r+11*r*r+r**3)/(1-r)**5

    Dm = 4*fam.rm/(1-fam.rm**2)
    Dp = 4*fam.rp/(1-fam.rp**2)
    alpha = -fam.ek*p2(fam.q)/2
    beta = -((1-fam.lam)*p2(fam.rm)/Dm + fam.lam*p2(fam.rp)/Dp)/2
    M4a = fam.ek*s4(fam.q)/12
    M4b = ((1-fam.lam)*s4(fam.rm)/Dm + fam.lam*s4(fam.rp)/Dp)/12
    aa = max(abs(lo(alpha)), abs(hi(alpha)))
    bb = max(abs(lo(beta)), abs(hi(beta)))
    return (aa + hi(M4a)*L0**2, 2*aa + 4*hi(M4a)*L0**2,
            bb + hi(M4b)*L0**2, 2*bb + 4*hi(M4b)*L0**2)


def certify_candidate_right_corner_upper(L0=mp.mpf(".35")):
    """Prove d*partial_t F<0 whenever the left endpoint is >=pi-L0."""
    Ca, Da, Cb, Db = candidate_edge_density_constants(L0)

    def data(C, D):
        mass = 1-C*L0**2
        assert mass > 0
        eps = 2*C*L0**2/mass
        eta = D*L0**2/mass + (1+C*L0**2)*D*L0**2/mass**2
        return mass, eps, eta

    ma, ea, na = data(Ca, Da)
    mb, eb, nb = data(Cb, Db)
    E = ea+eb+ea*eb
    DD = na*(1+eb)+nb*(1+ea)
    P = (1+ea)*(1+eb)
    cL = 1-L0**2/mp.pi**2
    bound = L0**2*(Da/ma+Db/mb) + 3*DD + (4*mp.log(2)-1)*E
    bound += DD*5*L0**2/(24*cL) + P*5*L0**2/(12*cL)
    assert bound < 1
    return 1-bound


def certify_candidate_top_upper(s_step=mp.mpf(".02"),
                                p_step=mp.mpf(".01"), pmax=mp.mpf(".05")):
    """Finite outward cover for t>=pi-pmax away from the right corner."""
    s = mp.mpf(0)
    evaluations = 0
    while s < PI-mp.mpf(".35"):
        shi = min(PI-mp.mpf(".35"), s+s_step)
        p = mp.mpf(0)
        while p < pmax:
            phi = min(pmax, p+p_step)
            value = upper_derivative_st_box(
                QSTAR_LO, QSTAR_HI, s, shi, PI-phi, PI-p, N=20, M=24
            )
            evaluations += 1
            if value is None or hi(value) >= 0:
                return False, (s, shi, p, phi, value, evaluations)
            p = phi
        s = shi
    return True, evaluations


_trig_cache = {}


def trig_tail(kind, p, N, x):
    """Directed C_p or S_p tail at a point Arb angle."""
    key = (kind, p, N, str(x))
    if key in _trig_cache:
        return _trig_cache[key]
    z = acb(0, x).exp().polylog(p)
    total = z.real if kind == "C" else z.imag
    for n in range(1, N + 1):
        term = (n * x).cos() if kind == "C" else (n * x).sin()
        total -= term / (n**p)
    _trig_cache[key] = total
    return total


def density_derivative(fam, theta, M=40):
    outa, outb = arb(0), arb(0)
    _, _, eta, xi, _, _ = normalized_coefficients(fam, M)
    for m in range(1, M + 1):
        sn = (m * theta).sin()
        outa += 2 * eta[m] * m * sn
        outb += 2 * xi[m] * m * sn
    # Geometric derivative tails at M=40 are below 1e-31.
    return outa + symmetric_error("1e-30"), outb + symmetric_error("1e-30")


def upper_derivative_corrected_point(fam, left, right, N=16, M=28):
    """Boundary-subtracted center value with rigorous residual tails."""
    qmass, rmass, X, Y = fourier_data(fam, left, right, N, M)
    at, bt = densities(fam, right)
    ass, bss = densities(fam, left)
    apt, bpt = density_derivative(fam, right)
    aps, bps = density_derivative(fam, left)
    logH = fam.H.log()
    energy = logH * qmass * rmass
    peta = logH * qmass
    pxi = logH * rmass
    for n, (xn, yn) in enumerate(zip(X, Y), 1):
        energy -= 2 * xn * yn / n
        ct = (n * right).cos()
        peta -= 2 * ct * yn / n
        pxi -= 2 * ct * xn / n

    endpoints = (left, right)
    ca = (-ass, at)
    cb = (-bss, bt)
    da = (-aps, apt)
    db = (-bps, bpt)

    def potential_Z(cvec, dvec, x):
        z = arb(0)
        for idx, (e, ce, de) in enumerate(zip(endpoints, cvec, dvec)):
            difference = arb(0) if idx == 1 else e - x
            z += ce * (trig_tail("S", 2, N, e + x)
                       + trig_tail("S", 2, N, difference)) / (2 * arb.pi())
            z += de * (trig_tail("C", 3, N, e + x)
                       + trig_tail("C", 3, N, difference)) / (2 * arb.pi())
        return z

    peta -= 2 * potential_Z(ca, da, right)
    pxi -= 2 * potential_Z(cb, db, right)

    zz = arb(0)
    for ie, (e, cae, cbe_dummy, dae, dbe_dummy) in enumerate(zip(endpoints, ca, cb, da, db)):
        del cbe_dummy, dbe_dummy
        for ih, (h, cbh, dbh) in enumerate(zip(endpoints, cb, db)):
            difference = arb(0) if ie == ih else e - h
            reverse_difference = arb(0) if ie == ih else h - e
            zz += cae * cbh * (trig_tail("C", 3, N, difference)
                                - trig_tail("C", 3, N, e + h)) / (2 * arb.pi()**2)
            zz += cae * dbh * (trig_tail("S", 4, N, e + h)
                                + trig_tail("S", 4, N, difference)) / (2 * arb.pi()**2)
            zz += dae * cbh * (trig_tail("S", 4, N, h + e)
                                + trig_tail("S", 4, N, reverse_difference)) / (2 * arb.pi()**2)
            zz += dae * dbh * (trig_tail("C", 5, N, difference)
                                + trig_tail("C", 5, N, e + h)) / (2 * arb.pi()**2)
    energy -= 2 * zz

    width = hi(right - left)
    Sa2 = hi(2 * fam.ek * fam.q * (1 + fam.q) / (1 - fam.q)**3)
    Dm = 4 * fam.rm / (1 - fam.rm**2)
    Dp = 4 * fam.rp / (1 - fam.rp**2)
    Sb2 = hi(2 * (
        (1 - fam.lam) * fam.rm * (1 + fam.rm) / ((1 - fam.rm)**3 * Dm)
        + fam.lam * fam.rp * (1 + fam.rp) / ((1 - fam.rp)**3 * Dp)
    ))
    Va, Vb = width * Sa2, width * Sb2
    Ua, Ub = hi(ass + at), hi(bss + bt)
    Uap, Ubp = hi(abs(aps) + abs(apt)), hi(abs(bps) + abs(bpt))
    qmin, rmin = lo(qmass), lo(rmass)
    if qmin <= 0 or rmin <= 0:
        return None
    S3 = mp.mpf(1) / (2 * N**2)
    S4 = mp.mpf(1) / (3 * N**3)
    S5 = mp.mpf(1) / (4 * N**4)
    eps_pa = 2 * Va / (mp.pi * qmin) * S3
    eps_pb = 2 * Vb / (mp.pi * rmin) * S3
    eps_e = 2 / (mp.pi**2 * qmin * rmin) * (
        (Ua * Vb + Ub * Va) * S4
        + (Uap * Vb + Ubp * Va + Va * Vb) * S5
    )

    avg = energy / (qmass * rmass)
    deriv = (at / (arb.pi() * qmass) * (pxi / rmass - avg - 1)
             + bt / (arb.pi() * rmass) * (peta / qmass - avg - 1))
    residual = (hi(at) / (mp.pi * qmin) * (eps_pb + eps_e)
                + hi(bt) / (mp.pi * rmin) * (eps_pa + eps_e)
                + mp.mpf("1e-10"))
    return deriv + symmetric_error(residual)


def mass_density_box(fam, left, right, M=24):
    # Only masses are needed for the explicit final tail propagation.
    qmass, rmass, _, _ = fourier_data(fam, left, right, N=0, M=M)
    at, bt = densities(fam, right)
    return qmass, rmass, at, bt


def upper_derivative_taylor_box(qlo, qhi, dlo, dhi, ylo, yhi,
                                N=240, M=24):
    """Mean-value endpoint enclosure with an explicit outer Fourier tail."""
    fam = family_box(qlo, qhi)
    dc, yc = (dlo + dhi) / 2, (ylo + yhi) / 2
    d0, y0 = B(dc), B(yc)
    left0 = (arb.pi() - d0) * y0
    right0 = left0 + d0
    center = upper_derivative_corrected_point(fam, left0, right0, N, M)
    if center is None:
        return None

    d = AD2(B(dlo, dhi), (arb(1), arb(0)))
    y = AD2(B(ylo, yhi), (arb(0), arb(1)))
    left = (arb.pi() - d) * y
    right = left + d
    jet = upper_derivative_raw(fam, left, right, N, M)
    variation = mp.mpf(0)
    for grad, radius in zip(jet.gradient, ((dhi - dlo) / 2, (yhi - ylo) / 2)):
        if not grad.is_finite():
            return None
        variation += max(abs(lo(grad)), abs(hi(grad))) * radius

    # Differentiating the boundary-subtracted tails (E)--(F) and using
    # |C_p'|,|S_p'| <= S_{p-1}(N) gives the following deliberately coarse
    # endpoint Lipschitz remainder.  It is used only on d>=0.1; the scaled
    # endpoint charts cover the diagonal.
    if dlo <= 0:
        return None
    tail_lipschitz = 100 / (N * dlo**2)
    tail_variation = tail_lipschitz * (
        (dhi - dlo) / 2 + mp.pi * (yhi - ylo) / 2
    )
    return center + symmetric_error(variation + tail_variation + mp.mpf("1e-10"))


def upper_derivative_st_box(qlo, qhi, slo, shi, tlo, thi, N=10, M=24):
    """Mean-value enclosure in the physical angle endpoints (s,t)."""
    if tlo <= shi:
        return None
    fam = family_box(qlo, qhi)
    sc, tc = (slo + shi) / 2, (tlo + thi) / 2
    center = upper_derivative_corrected_point(fam, B(sc), B(tc), N, M)
    if center is None:
        return None
    s = AD2(B(slo, shi), (arb(1), arb(0)))
    t = AD2(B(tlo, thi), (arb(0), arb(1)))
    jet = upper_derivative_raw(fam, s, t, N, M)
    variation = mp.mpf(0)
    for grad, radius in zip(jet.gradient, ((shi - slo) / 2, (thi - tlo) / 2)):
        if not grad.is_finite():
            return None
        variation += max(abs(lo(grad)), abs(hi(grad))) * radius
    dmin = tlo - shi
    # Boundary-tail differentiation from (E)--(F); on the compact driver
    # dmin>=0.3.  The displayed constant is the sum of the four endpoint
    # coefficient bounds after the normalized densities are <=1.1.
    tail_variation = 100 / (N * dmin**2) * ((shi - slo) + (thi - tlo)) / 2
    return center + symmetric_error(variation + tail_variation + mp.mpf("1e-10"))


def upper_derivative_compact_box(qlo, qhi, slo, shi, zlo, zhi,
                                 N=10, M=24):
    """Compact chart: d=.3+z(pi-.6-s), t=s+d."""
    fam = family_box(qlo, qhi)
    sc, zc = (slo + shi) / 2, (zlo + zhi) / 2
    dc = mp.mpf(".3") + zc * (mp.pi - mp.mpf(".6") - sc)
    tc = sc + dc
    center = upper_derivative_corrected_point(fam, B(sc), B(tc), N, M)
    if center is None:
        return None

    s = AD2(B(slo, shi), (arb(1), arb(0)))
    z = AD2(B(zlo, zhi), (arb(0), arb(1)))
    d = arb(".3") + z * (arb.pi() - arb(".6") - s)
    t = s + d
    jet = upper_derivative_raw(fam, s, t, N, M)
    variation = mp.mpf(0)
    for grad, radius in zip(jet.gradient, ((shi - slo) / 2, (zhi - zlo) / 2)):
        if not grad.is_finite():
            return None
        variation += max(abs(lo(grad)), abs(hi(grad))) * radius
    # The compact chart has d>=.3.  Convert chart radii to endpoint motion.
    dmin = mp.mpf(".3") + zlo * (mp.pi - mp.mpf(".6") - shi)
    endpoint_motion = ((shi - slo) / 2
                       + mp.pi * (zhi - zlo) / 2)
    tail_variation = 100 / (N * dmin**2) * endpoint_motion
    return center + symmetric_error(variation + tail_variation + mp.mpf("1e-10"))


def upper_derivative_box(qlo, qhi, dlo, dhi, ylo, yhi, N=160, M=18):
    fam = family_box(qlo, qhi)
    d = B(dlo, dhi)
    y = B(ylo, yhi)
    left = (arb.pi() - d) * y
    right = left + d
    qmass, rmass, X, Y = fourier_data(fam, left, right, N=N, M=M)
    if lo(qmass) <= 0 or lo(rmass) <= 0:
        return None

    at, bt = densities(fam, right)
    if lo(at) <= 0 or lo(bt) < 0:
        return None
    logH = fam.H.log()
    energy = logH * qmass * rmass
    peta = logH * qmass
    pxi = logH * rmass
    for n, (xn, yn) in enumerate(zip(X, Y), 1):
        energy -= 2 * xn * yn / n
        ct = (n * right).cos()
        peta -= 2 * ct * yn / n
        pxi -= 2 * ct * xn / n

    # Explicit outer Fourier tails.
    e_tail = 4 * hi(at) * hi(bt) / (mp.pi**2 * N**2)
    peta_tail = 4 * hi(at) / (mp.pi * N)
    pxi_tail = 4 * hi(bt) / (mp.pi * N)
    energy += symmetric_error(e_tail)
    peta += symmetric_error(peta_tail)
    pxi += symmetric_error(pxi_tail)

    avg = energy / (qmass * rmass)
    deriv = at / (arb.pi() * qmass) * (pxi / rmass - avg - 1) \
        + bt / (arb.pi() * rmass) * (peta / qmass - avg - 1)
    return deriv


def point_test():
    # A zero-radius parameter/endpoints box must reproduce a strict sign.
    q = mp.mpf("0.02571553686652745")
    v = upper_derivative_box(q, q, mp.mpf(1), mp.mpf(1),
                             mp.mpf("0.4669422069"), mp.mpf("0.4669422069"),
                             N=400, M=24)
    assert v is not None and hi(v) < 0


def compact_physical_bounds(slo, shi, zlo, zhi):
    L = PI - mp.mpf(".6")
    rows = []
    for s in (slo, shi):
        for z in (zlo, zhi):
            d = mp.mpf(".3") + z * (L - s)
            rows.append((s, s + d, d))
    return (min(x[0] for x in rows), max(x[0] for x in rows),
            min(x[1] for x in rows), max(x[1] for x in rows),
            min(x[2] for x in rows), max(x[2] for x in rows))


def certify_compact_interior(max_depth=14, q_step=mp.mpf("1e-4")):
    """Adaptive outward driver for s,t>=.3 and t-s>=.3.

    Returns (True, statistics) only after every q slab and endpoint box is
    exhausted.  Otherwise it returns the first exact unresolved box.
    """
    qlo = Q_LO
    total_evaluations = 0
    while qlo < Q_HI:
        qhi = min(Q_HI, qlo + q_step)
        stack = [(mp.mpf(".3"), PI - mp.mpf(".6"),
                  mp.mpf(0), mp.mpf(1), 0)]
        while stack:
            slo, shi, zlo, zhi, depth = stack.pop()
            value = upper_derivative_compact_box(
                qlo, qhi, slo, shi, zlo, zhi, N=20, M=24
            )
            total_evaluations += 1
            if value is not None and hi(value) < 0:
                continue
            if depth >= max_depth:
                return False, {
                    "q": (qlo, qhi),
                    "s_chart": (slo, shi),
                    "z_chart": (zlo, zhi),
                    "physical": compact_physical_bounds(slo, shi, zlo, zhi),
                    "derivative": value,
                    "evaluations": total_evaluations,
                }
            if (shi - slo) / (PI - mp.mpf(".9")) >= zhi - zlo:
                mid = (slo + shi) / 2
                stack.extend(((slo, mid, zlo, zhi, depth + 1),
                              (mid, shi, zlo, zhi, depth + 1)))
            else:
                mid = (zlo + zhi) / 2
                stack.extend(((slo, shi, zlo, mid, depth + 1),
                              (slo, shi, mid, zhi, depth + 1)))
        qlo = qhi
    return True, {"evaluations": total_evaluations}


def main():
    point_test()
    passed, report = certify_compact_interior()
    if passed:
        print("PASS: compact interior upper-endpoint derivative")
        print("boxes evaluated =", report["evaluations"])
        return
    print("UNRESOLVED: compact interior upper-endpoint derivative")
    print("q box =", report["q"])
    print("s-chart box =", report["s_chart"])
    print("z-chart box =", report["z_chart"])
    print("physical (s_lo,s_hi,t_lo,t_hi,d_lo,d_hi) =", report["physical"])
    print("derivative enclosure =", report["derivative"])
    print("boxes evaluated =", report["evaluations"])


if __name__ == "__main__":
    main()
'''


# ============================================================================
# EMBEDDED SOURCE: negative_platform_fourier.py
# ============================================================================
SOURCES["negative_platform_fourier.py"] = r'''#!/usr/bin/env python3
"""General negative-platform reference data in the mixed Fourier chart.

This module is intentionally separate from the uniform verifier.  It converts
(k,a,C_eff) and the two main crossings into the endpoint-normalized ``Family``
used by ``verify_mixed_interval_derivative_signs.py``.  Point solves are
diagnostic starts; a uniform proof must replace their small pads by interval
Newton/Krawczyk boxes in (k,a,x_minus,x_plus).
"""

from dataclasses import dataclass
import math

import mpmath as mp
from scipy.optimize import brentq



mp.mp.dps = 70
LSTAR = mp.mpf("1.83443047576266171109075363512478614")


@dataclass
class NegativePlatformData:
    k: mp.mpf
    a: mp.mpf
    xminus: mp.mpf
    xplus: mp.mpf
    sigma_minus: mp.mpf
    sigma_plus: mp.mpf
    C: mp.mpf
    M0: mp.mpf
    rtotal: mp.mpf
    Ceff: mp.mpf
    api: mp.mpf
    family: core.Family

    @property
    def ceff_normalized(self):
        """Coefficient in F_adjusted=F-Ceff/(api*q_normalized)."""
        return self.Ceff / self.api

    @property
    def circle_scalar(self):
        """Global lower bound for every adjusted mixed interval.

        See ``circle_bathtub_mixed_interval_lemma.md``.  The ``Family``
        parameters may be Arb boxes, while ``ceff_normalized`` is a point in
        this diagnostic module.  Uniform callers should interval-evaluate
        the corresponding expression from their joint parameter boxes.
        """
        return ((2 * self.family.H).log() - self.family.logscale
                - core.B(self.ceff_normalized))


def external_data(k, a):
    k, a = mp.mpf(k), mp.mpf(a)
    c = (a+2)/2
    radius = (2-a)/2
    H = radius/2
    K0 = mp.sqrt(2*a)
    rho0 = (c-K0)/radius

    def moment(x):
        Kx = mp.sqrt((a-x)*(2-x))
        rhox = (c-x-Kx)/radius
        return mp.log((c-x+Kx)/2) - 2*k*mp.log(1-rho0*rhox)

    def moment_prime(x):
        Kx = mp.sqrt((a-x)*(2-x))
        rhox = (c-x-Kx)/radius
        return -1/Kx + 2*k*rho0*rhox/(Kx*(1-rho0*rhox))

    def W(x): return k*mp.log(abs(x))+moment(x)
    def Wprime(x): return k/x+moment_prime(x)
    return c, radius, H, rho0, W, Wprime


def solve_crossings(k, a):
    c, radius, H, rho0, W, Wprime = external_data(k, a)
    kf, af = float(k), float(a)
    Wf = lambda x: float(W(mp.mpf(x)))
    Wpf = lambda x: float(Wprime(mp.mpf(x)))
    left = -1.0
    while Wf(left) < 0:
        left *= 2
    xm0 = brentq(Wf, left, -1e-12)
    critical = brentq(Wpf, 1e-12, af-1e-12)
    if Wf(critical) <= 0:
        raise ValueError("main component is not separated")
    xp0 = brentq(Wf, 1e-12, critical)
    xm = mp.findroot(W, (mp.mpf(xm0-.001), mp.mpf(xm0+.001)))
    xp = mp.findroot(W, (mp.mpf(xp0-.001), mp.mpf(xp0+.001)))
    return xm, xp


def make_data(k, a, target=LSTAR):
    k, a, target = mp.mpf(k), mp.mpf(a), mp.mpf(target)
    c, radius, H, rho0, W, Wprime = external_data(k, a)
    xm, xp = solve_crossings(k, a)
    sm, sp = -1/Wprime(xm), 1/Wprime(xp)
    Km, Kp = mp.sqrt((a-xm)*(2-xm)), mp.sqrt((a-xp)*(2-xp))
    rm, rp = (c-xm-Km)/radius, (c-xp-Kp)/radius
    bpi = 4*sm*rm/(1-rm**2)+4*sp*rp/(1-rp**2)
    lam = (4*sp*rp/(1-rp**2))/bpi
    api = 1+2*k*rho0/(1+rho0)
    C = mp.log((2-a)/4)+k*mp.log((a+2+2*mp.sqrt(2*a))/4)
    M0 = xp-xm
    D = sm*(1+rm)/(1-rm)+sp*(1+rp)/(1-rp)
    rtotal = D-sm-sp
    Ceff = C+(target-M0)/rtotal

    # Diagnostic point balls.  The forthcoming uniform verifier must enlarge
    # these from a certified joint root box, not merely trust the pad.
    pad = mp.mpf("1e-35")
    family = core.Family(
        core.B(rho0-pad, rho0+pad), core.B(H-pad, H+pad),
        core.B(k/api-pad, k/api+pad), core.B(lam-pad, lam+pad),
        core.B(rp-pad, rp+pad), core.B(rm-pad, rm+pad),
        core.B(mp.log(api*bpi)-pad, mp.log(api*bpi)+pad),
    )
    return NegativePlatformData(k, a, xm, xp, sm, sp, C, M0,
                                rtotal, Ceff, api, family)


def solve_aL(k, target=LSTAR):
    k, target = mp.mpf(k), mp.mpf(target)
    amin = max(mp.mpf(1), 2*(k/(k+1))**2)+mp.mpf("1e-8")

    def width_defect(a):
        xm, xp = solve_crossings(k, a)
        return xp-xm-target

    # Locate the right-hand branch with a short double-precision scan.
    grid = [amin+(mp.mpf("1.999999")-amin)*j/100 for j in range(101)]
    brackets = []
    last = None
    for x in grid:
        try: value = width_defect(x)
        except Exception: continue
        if last is not None and last[1]*value < 0:
            brackets.append((last[0], x))
        last = x, value
    if not brackets:
        raise ValueError("no a_L root found")
    lo, hi = brackets[-1]
    return mp.findroot(width_defect, (lo, hi))


def adjusted_margin_point(data, s, t, N=1200, M=28):
    s, t = core.B(s), core.B(t)
    base = core.mixed_margin_raw(data.family, s, t, N, M)
    qmass, _, _, _ = core.fourier_data(data.family, s, t, N=0, M=M)
    return base-data.ceff_normalized/qmass


def adjusted_upper_raw(data, left, right, N=20, M=24):
    base = core.upper_derivative_raw(data.family, left, right, N, M)
    qmass, _, _, _ = core.fourier_data_raw(data.family, left, right, N=0, M=M)
    at, _ = core.densities(data.family, right)
    return base + data.ceff_normalized * at / (core.arb.pi() * qmass**2)


def adjusted_upper_point(data, left, right, N=20, M=24):
    base = core.upper_derivative_corrected_point(data.family, left, right, N, M)
    if base is None:
        return None
    qmass, _, _, _ = core.fourier_data(data.family, left, right, N=0, M=M)
    at, _ = core.densities(data.family, right)
    return base + data.ceff_normalized * at / (core.arb.pi() * qmass**2)


def adjusted_upper_st_box(data, slo, shi, tlo, thi, N=12, M=24):
    if tlo <= shi:
        return None
    sc, tc = (slo+shi)/2, (tlo+thi)/2
    center = adjusted_upper_point(data, core.B(sc), core.B(tc), N, M)
    if center is None:
        return None
    s = core.AD2(core.B(slo, shi), (core.arb(1), core.arb(0)))
    t = core.AD2(core.B(tlo, thi), (core.arb(0), core.arb(1)))
    jet = adjusted_upper_raw(data, s, t, N, M)
    variation = mp.mpf(0)
    for grad, radius in zip(jet.gradient, ((shi-slo)/2, (thi-tlo)/2)):
        if not grad.is_finite():
            return None
        variation += max(abs(core.lo(grad)), abs(core.hi(grad)))*radius
    dmin = tlo-shi
    variation += 100/(N*dmin**2)*((shi-slo)+(thi-tlo))/2
    return center+core.symmetric_error(variation+mp.mpf("1e-10"))


if __name__ == "__main__":
    for k in (mp.mpf("2.3"), mp.mpf("3"), mp.mpf("4.2"),
              mp.mpf("4.6987112748508944"), mp.mpf("5.3")):
        a = solve_aL(k)
        data = make_data(k, a)
        print("k,a,C,Ceff,M0 =", k, a, data.C, data.Ceff, data.M0)
        print("circle scalar =", data.circle_scalar)
        print("full adjusted F =", adjusted_margin_point(data, 0, mp.pi, 600))
'''


# ============================================================================
# EMBEDDED SOURCE: verify_onecut_global.py
# ============================================================================
SOURCES["verify_onecut_global.py"] = r'''#!/usr/bin/env python3
"""Deterministic interval certificate for the complete terminal one-cut family.

The theorem certified here is deliberately restricted to the zero-slack
terminal-interval ansatz.  It proves:

* the admissible parameter interval is 0 < q <= q_soft;
* both exterior zero branches exist and are unique throughout that interval;
* the associated length has exactly one stationary point;
* that point is the strict global minimum of the one-cut family.

All transcendental interval evaluations use outward-rounded ``mpmath.iv``.
The singular q -> 0 end is treated in r=1/(-log q), z=q*u coordinates.
The soft edge is treated with y=(log u_plus)^2, which analytically deflates
the coalescence of the plus root with u=1.

This script is not a global certificate over arbitrary compact conductors.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial

import mpmath as mp
from mpmath import iv

if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


mp.mp.dps = 90
iv.dps = 90

LN2 = mp.log(2)
Q_GEOM = 3 - 2 * mp.sqrt(2)
Q_SOFT_CENTER = mp.mpf(
    "0.1236306846493834978974060904264788695442437883724"
)
Q_SOFT_RADIUS = mp.mpf("1e-48")
Q_STAR_CENTER = mp.mpf(
    "0.02571553686652745032257637166391965344"
)
R_STAR_CENTER = -1 / mp.log(Q_STAR_CENTER)


def I(lo, hi=None):
    """Make a decimal interval without a binary-float conversion."""
    if hi is None:
        lo = mp.mpf(lo)
        if lo == 0:
            return iv.mpf(0)
        guard = mp.mpf("1e-85") * (1 + abs(lo))
        return iv.mpf([mp.nstr(lo - guard, 100), mp.nstr(lo + guard, 100)])
    lo, hi = mp.mpf(lo), mp.mpf(hi)
    guard = mp.mpf("1e-85") * (1 + max(abs(lo), abs(hi)))
    left = lo if lo == 0 else lo - guard
    right = hi if hi == 0 else hi + guard
    return iv.mpf([mp.nstr(left, 100), mp.nstr(right, 100)])


def bounds(x):
    body = str(x).strip()[1:-1]
    left, right = body.split(",")
    left = mp.mpf(left.strip())
    right = mp.mpf(right.strip())
    # Parsing a printed endpoint back into mp.mpf must not make an interval
    # microscopically narrower.  At iv.dps=90 this guard is many orders above
    # the print/parse error and many orders below every certified margin.
    guard = mp.mpf("1e-85") * (1 + max(abs(left), abs(right)))
    return left - guard, right + guard


def lower(x):
    return bounds(x)[0]


def upper(x):
    return bounds(x)[1]


def positive(x):
    return lower(x) > 0


def negative(x):
    return upper(x) < 0


def intersect(a, b):
    alo, ahi = bounds(a)
    blo, bhi = bounds(b)
    lo, hi = max(alo, blo), min(ahi, bhi)
    if lo > hi:
        raise ValueError("empty interval intersection")
    return I(lo, hi)


@dataclass
class Jet:
    """Second-order interval jet; only first order is used at the soft edge."""

    value: object
    gradient: list[object]
    hessian: list[list[object]]

    @staticmethod
    def constant(value, dim=3):
        return Jet(
            iv.mpf(value),
            [iv.mpf(0) for _ in range(dim)],
            [[iv.mpf(0) for _ in range(dim)] for _ in range(dim)],
        )

    @staticmethod
    def variable(value, index, dim=3):
        out = Jet.constant(value, dim)
        out.gradient[index] = iv.mpf(1)
        return out

    def coerce(self, other):
        return other if isinstance(other, Jet) else Jet.constant(other, len(self.gradient))

    def __add__(self, other):
        other = self.coerce(other)
        n = len(self.gradient)
        return Jet(
            self.value + other.value,
            [self.gradient[i] + other.gradient[i] for i in range(n)],
            [
                [self.hessian[i][j] + other.hessian[i][j] for j in range(n)]
                for i in range(n)
            ],
        )

    __radd__ = __add__

    def __neg__(self):
        return Jet(
            -self.value,
            [-x for x in self.gradient],
            [[-x for x in row] for row in self.hessian],
        )

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        n = len(self.gradient)
        value = self.value * other.value
        gradient = [
            self.gradient[i] * other.value + self.value * other.gradient[i]
            for i in range(n)
        ]
        hessian = []
        for i in range(n):
            row = []
            for j in range(n):
                row.append(
                    self.hessian[i][j] * other.value
                    + self.gradient[i] * other.gradient[j]
                    + self.gradient[j] * other.gradient[i]
                    + self.value * other.hessian[i][j]
                )
            hessian.append(row)
        return Jet(value, gradient, hessian)

    __rmul__ = __mul__

    def reciprocal(self):
        n = len(self.gradient)
        value = 1 / self.value
        gradient = [-x / self.value**2 for x in self.gradient]
        hessian = []
        for i in range(n):
            row = []
            for j in range(n):
                row.append(
                    2 * self.gradient[i] * self.gradient[j] / self.value**3
                    - self.hessian[i][j] / self.value**2
                )
            hessian.append(row)
        return Jet(value, gradient, hessian)

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise TypeError("integer powers only")
        if exponent == 0:
            return Jet.constant(1, len(self.gradient))
        if exponent < 0:
            return (self ** (-exponent)).reciprocal()
        result = Jet.constant(1, len(self.gradient))
        base = self
        n = exponent
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n >>= 1
        return result


def jlog(x):
    if not isinstance(x, Jet):
        return iv.log(x)
    n = len(x.gradient)
    return Jet(
        iv.log(x.value),
        [g / x.value for g in x.gradient],
        [
            [
                x.hessian[i][j] / x.value
                - x.gradient[i] * x.gradient[j] / x.value**2
                for j in range(n)
            ]
            for i in range(n)
        ],
    )


def jexp(x):
    if not isinstance(x, Jet):
        return iv.exp(x)
    n = len(x.gradient)
    value = iv.exp(x.value)
    return Jet(
        value,
        [value * g for g in x.gradient],
        [
            [
                value * (x.hessian[i][j] + x.gradient[i] * x.gradient[j])
                for j in range(n)
            ]
            for i in range(n)
        ],
    )


@dataclass
class FirstJet:
    """Lightweight first-order jet used by the soft-edge subdivision."""

    value: object
    gradient: list[object]

    @staticmethod
    def constant(value, dim=3):
        return FirstJet(iv.mpf(value), [iv.mpf(0) for _ in range(dim)])

    @staticmethod
    def variable(value, index, dim=3):
        out = FirstJet.constant(value, dim)
        out.gradient[index] = iv.mpf(1)
        return out

    def coerce(self, other):
        return other if isinstance(other, FirstJet) else FirstJet.constant(other, len(self.gradient))

    def __add__(self, other):
        other = self.coerce(other)
        return FirstJet(
            self.value + other.value,
            [x + y for x, y in zip(self.gradient, other.gradient)],
        )

    __radd__ = __add__

    def __neg__(self):
        return FirstJet(-self.value, [-x for x in self.gradient])

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return FirstJet(
            self.value * other.value,
            [
                self.gradient[i] * other.value + self.value * other.gradient[i]
                for i in range(len(self.gradient))
            ],
        )

    __rmul__ = __mul__

    def reciprocal(self):
        return FirstJet(
            1 / self.value,
            [-x / self.value**2 for x in self.gradient],
        )

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()

    def __pow__(self, exponent):
        if exponent == 0:
            return FirstJet.constant(1, len(self.gradient))
        if exponent < 0:
            return (self ** (-exponent)).reciprocal()
        result = FirstJet.constant(1, len(self.gradient))
        base, n = self, exponent
        while n:
            if n & 1:
                result *= base
            base *= base
            n >>= 1
        return result


def first_log(x):
    if not isinstance(x, FirstJet):
        return iv.log(x)
    return FirstJet(iv.log(x.value), [g / x.value for g in x.gradient])


def point_parameters_r(r):
    q = mp.exp(-1 / r)
    d = LN2 - 2 * mp.log(1 + q)
    A = 1 - r * d
    return q, d, A


def point_G(r, z, minus):
    q, d, A = point_parameters_r(r)
    denominator = z - 1 if minus else 1 - z
    return A * mp.log((z - q * q) / denominator) - mp.log(z) - d


def bisect(f, lo, hi, iterations=180):
    flo, fhi = f(lo), f(hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if flo * fhi > 0:
        raise ValueError("root is not bracketed")
    for _ in range(iterations):
        mid = (lo + hi) / 2
        fm = f(mid)
        if flo * fm <= 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return (lo + hi) / 2


def point_roots_r(r):
    q, _, A = point_parameters_r(r)
    B = 1 + q * q - A * (1 - q * q)
    critical = (B + mp.sqrt(B * B - 4 * q * q)) / 2
    zp = bisect(lambda z: point_G(r, z, False), critical, 1 - mp.mpf("1e-70"))
    zm = bisect(lambda z: point_G(r, z, True), 1 + mp.mpf("1e-70"), 3)
    return zp, zm


def bulk_jets(r_box, zp_box, zm_box):
    r = Jet.variable(r_box, 0)
    zp = Jet.variable(zp_box, 1)
    zm = Jet.variable(zm_box, 2)
    q = jexp(-1 / r)
    d = Jet.constant(iv.log(2)) - 2 * jlog(1 + q)
    A = 1 - r * d

    def G(z, minus):
        denominator = z - 1 if minus else 1 - z
        return A * jlog((z - q * q) / denominator) - jlog(z) - d

    gp = G(zp, False)
    gm = G(zm, True)
    h = 2 / (1 + q) ** 2
    k = 2 * q * q / (1 + q) ** 2
    length = h * (zm - zp) + k * (1 / zm - 1 / zp)
    return gp, gm, length


def root_boxes_r(rlo, rhi):
    samples = [point_roots_r(x) for x in (rlo, (rlo + rhi) / 2, rhi)]
    width = rhi - rlo
    # Direct interval evaluation of G contains cancellation of O(width)
    # terms.  An O(width) guard (not merely the true O(width^2) curvature
    # error) gives endpoint signs that remain strict under that dependency.
    pad = max(mp.mpf("1e-50"), 8 * width)
    zp_values = [x[0] for x in samples]
    zm_values = [x[1] for x in samples]
    return (
        I(min(zp_values) - pad, max(zp_values) + pad),
        I(min(zm_values) - pad, max(zm_values) + pad),
    )


def bulk_first_data(r_box, z, minus):
    """Fast first-order interval formulas in the stable (r,z) chart."""
    q = iv.exp(-1 / r_box)
    q_r = q / r_box**2
    d = iv.log(2) - 2 * iv.log(1 + q)
    d_r = -2 * q_r / (1 + q)
    A = 1 - r_box * d
    A_r = -d - r_box * d_r
    denominator = z - 1 if minus else 1 - z
    W = iv.log((z - q * q) / denominator)
    W_z = 1 / (z - q * q) + (1 / (1 - z) if not minus else -1 / (z - 1))
    W_r = -2 * q * q_r / (z - q * q)
    G = A * W - iv.log(z) - d
    G_z = A * W_z - 1 / z
    G_r = A_r * W + A * W_r - d_r
    return G, G_z, G_r, -G_r / G_z, q, q_r


def certify_bulk_first(rlo, rhi, want_sign):
    r_box = I(rlo, rhi)
    zp_box, zm_box = root_boxes_r(rlo, rhi)
    gp = bulk_first_data(r_box, zp_box, False)
    gm = bulk_first_data(r_box, zm_box, True)
    roots_ok = (
        negative(bulk_first_data(r_box, I(lower(zp_box)), False)[0])
        and positive(bulk_first_data(r_box, I(upper(zp_box)), False)[0])
        and positive(gp[1])
        and positive(bulk_first_data(r_box, I(lower(zm_box)), True)[0])
        and negative(bulk_first_data(r_box, I(upper(zm_box)), True)[0])
        and negative(gm[1])
    )
    if not roots_ok:
        return False, None, None, (zp_box, zm_box)

    zp_center, zm_center = point_roots_r((rlo + rhi) / 2)
    for _ in range(2):
        gp = bulk_first_data(r_box, zp_box, False)
        gp_center = bulk_first_data(r_box, I(zp_center), False)[0]
        zp_box = intersect(zp_box, I(zp_center) - gp_center / gp[1])
        gm = bulk_first_data(r_box, zm_box, True)
        gm_center = bulk_first_data(r_box, I(zm_center), True)[0]
        zm_box = intersect(zm_box, I(zm_center) - gm_center / gm[1])

    gp = bulk_first_data(r_box, zp_box, False)
    gm = bulk_first_data(r_box, zm_box, True)
    zp_r, zm_r = gp[3], gm[3]
    q, q_r = gp[4], gp[5]
    h = 2 / (1 + q) ** 2
    k = 2 * q * q / (1 + q) ** 2
    h_r = -4 * q_r / (1 + q) ** 3
    k_r = 4 * q * q_r / (1 + q) ** 3
    length_r = (
        h_r * (zm_box - zp_box)
        + h * (zm_r - zp_r)
        + k_r * (1 / zm_box - 1 / zp_box)
        + k * (-zm_r / zm_box**2 + zp_r / zp_box**2)
    )
    sign_ok = True
    if want_sign == -1:
        sign_ok = negative(length_r)
    elif want_sign == 1:
        sign_ok = positive(length_r)
    return sign_ok, length_r, None, (zp_box, zm_box)


def certify_bulk_box(rlo, rhi, want_sign=None, want_second=False):
    if not want_second:
        return certify_bulk_first(rlo, rhi, want_sign)
    r_box = I(rlo, rhi)
    zp_box, zm_box = root_boxes_r(rlo, rhi)
    gp, gm, length = bulk_jets(r_box, zp_box, zm_box)

    # Uniform endpoint signs plus the derivative signs prove that the boxes
    # contain the unique desired roots for every parameter in r_box.
    gp_lo = bulk_jets(r_box, I(lower(zp_box)), zm_box)[0].value
    gp_hi = bulk_jets(r_box, I(upper(zp_box)), zm_box)[0].value
    gm_lo = bulk_jets(r_box, zp_box, I(lower(zm_box)))[1].value
    gm_hi = bulk_jets(r_box, zp_box, I(upper(zm_box)))[1].value
    roots_ok = (
        negative(gp_lo)
        and positive(gp_hi)
        and positive(gm_lo)
        and negative(gm_hi)
        and positive(gp.gradient[1])
        and negative(gm.gradient[2])
    )
    if not roots_ok:
        return False, None, None, (zp_box, zm_box)

    # The sign test above establishes containment.  A parametric interval
    # Newton contraction then removes the deliberately generous O(width)
    # guards before differentiating the length.  For every actual root,
    # the mean-value theorem puts it in the displayed Newton image.
    zp_center, zm_center = point_roots_r((rlo + rhi) / 2)
    for _ in range(2):
        gp_box = bulk_jets(r_box, zp_box, zm_box)[0]
        gp_center = bulk_jets(r_box, I(zp_center), zm_box)[0].value
        zp_newton = I(zp_center) - gp_center / gp_box.gradient[1]
        zp_box = intersect(zp_box, zp_newton)

        gm_box = bulk_jets(r_box, zp_box, zm_box)[1]
        gm_center = bulk_jets(r_box, zp_box, I(zm_center))[1].value
        zm_newton = I(zm_center) - gm_center / gm_box.gradient[2]
        zm_box = intersect(zm_box, zm_newton)

    gp, gm, length = bulk_jets(r_box, zp_box, zm_box)

    zp_r = -gp.gradient[0] / gp.gradient[1]
    zm_r = -gm.gradient[0] / gm.gradient[2]
    length_r = (
        length.gradient[0]
        + length.gradient[1] * zp_r
        + length.gradient[2] * zm_r
    )

    sign_ok = True
    if want_sign == -1:
        sign_ok = negative(length_r)
    elif want_sign == 1:
        sign_ok = positive(length_r)

    length_rr = None
    if want_second:
        zp_rr = -(
            gp.hessian[0][0]
            + 2 * gp.hessian[0][1] * zp_r
            + gp.hessian[1][1] * zp_r * zp_r
        ) / gp.gradient[1]
        zm_rr = -(
            gm.hessian[0][0]
            + 2 * gm.hessian[0][2] * zm_r
            + gm.hessian[2][2] * zm_r * zm_r
        ) / gm.gradient[2]
        length_rr = (
            length.hessian[0][0]
            + 2 * length.hessian[0][1] * zp_r
            + 2 * length.hessian[0][2] * zm_r
            + length.hessian[1][1] * zp_r * zp_r
            + 2 * length.hessian[1][2] * zp_r * zm_r
            + length.hessian[2][2] * zm_r * zm_r
            + length.gradient[1] * zp_rr
            + length.gradient[2] * zm_rr
        )
        sign_ok = sign_ok and positive(length_rr)

    return sign_ok, length_r, length_rr, (zp_box, zm_box)


def recursive_bulk(a, b, sign, second=False, depth=0):
    try:
        ok, first, second_value, _ = certify_bulk_box(a, b, sign, second)
    except (ValueError, ZeroDivisionError, mp.libmp.libmpf.ComplexResult):
        ok, first, second_value = False, None, None
    if ok:
        return [(a, b, first, second_value)]
    if depth >= 26:
        raise RuntimeError(f"bulk subdivision failed on [{a}, {b}]")
    mid = (a + b) / 2
    return recursive_bulk(a, mid, sign, second, depth + 1) + recursive_bulk(
        mid, b, sign, second, depth + 1
    )


def tail_certificate():
    """Uniform r in [0,.02] certificate using analytic q and q_r bounds."""
    r0 = mp.mpf("0.02")
    q0 = mp.exp(-1 / r0)
    qr0 = q0 / (r0 * r0)
    r = I(0, r0)
    q = I(0, q0)
    qr = I(0, qr0)
    d = iv.log(2) - 2 * iv.log(1 + q)
    A = 1 - r * d
    A_r = -d + 2 * r * qr / (1 + q)

    def data(z, minus):
        denominator = z - 1 if minus else 1 - z
        W = iv.log((z - q * q) / denominator)
        W_z = 1 / (z - q * q) + (1 / (1 - z) if not minus else -1 / (z - 1))
        W_r = -2 * q * qr / (z - q * q)
        G = A * W - iv.log(z) - d
        G_z = A * W_z - 1 / z
        G_r = A_r * W + A * W_r + 2 * qr / (1 + q)
        return G, G_z, G_r, -G_r / G_z

    zp = I(mp.mpf(".499"), mp.mpf(".501"))
    zm = I(mp.mpf("1.49"), mp.mpf("1.5001"))
    gp = data(zp, False)
    gm = data(zm, True)
    signs = [
        negative(data(I(mp.mpf(".499")), False)[0]),
        positive(data(I(mp.mpf(".501")), False)[0]),
        positive(gp[1]),
        positive(data(I(mp.mpf("1.49")), True)[0]),
        negative(data(I(mp.mpf("1.5001")), True)[0]),
        negative(gm[1]),
    ]
    h = 2 / (1 + q) ** 2
    k = 2 * q * q / (1 + q) ** 2
    h_r = -4 * qr / (1 + q) ** 3
    k_r = 4 * q * qr / (1 + q) ** 3
    zp_r, zm_r = gp[3], gm[3]
    length_r = (
        h_r * (zm - zp)
        + h * (zm_r - zp_r)
        + k_r * (1 / zm - 1 / zp)
        + k * (-zm_r / zm**2 + zp_r / zp**2)
    )
    return all(signs) and negative(length_r), length_r, q0, qr0


def add_series_remainder(partial, argument, value_bound, derivative_bound):
    """Attach a rigorous positive remainder and its first derivative."""
    partial.value += I(0, value_bound)
    multiplier = I(0, derivative_bound)
    partial.gradient = [
        g + multiplier * argument.gradient[i]
        for i, g in enumerate(partial.gradient)
    ]
    return partial


def factorial_series(argument, kind, terms=32):
    """C(y)=cosh(sqrt(y)) or S(y)=sinh(sqrt(y))/sqrt(y)."""
    cls = FirstJet if isinstance(argument, FirstJet) else Jet
    result = cls.constant(0)
    power = cls.constant(1)
    for k in range(terms + 1):
        denominator = factorial(2 * k if kind == "C" else 2 * k + 1)
        result += power / denominator
        power *= argument

    Y = upper(argument.value)
    K = terms + 1
    shift = 0 if kind == "C" else 1
    first = Y**K / mp.mpf(factorial(2 * K + shift))
    ratio = Y / ((2 * K + shift + 2) * (2 * K + shift + 1))
    value_bound = first / (1 - ratio)
    first_d = K * Y ** (K - 1) / mp.mpf(factorial(2 * K + shift))
    ratio_d = (
        mp.mpf(K + 1)
        / K
        * Y
        / ((2 * K + shift + 2) * (2 * K + shift + 1))
    )
    derivative_bound = first_d / (1 - ratio_d)
    return add_series_remainder(result, argument, value_bound, derivative_bound)


def atanhc_series(argument, terms=32):
    """T(w)=atanh(sqrt(w))/sqrt(w), analytic at w=0."""
    cls = FirstJet if isinstance(argument, FirstJet) else Jet
    result = cls.constant(0)
    power = cls.constant(1)
    for k in range(terms + 1):
        result += power / (2 * k + 1)
        power *= argument
    W = upper(argument.value)
    if W >= 1:
        raise ValueError("atanhc series left its disk of convergence")
    K = terms + 1
    first = W**K / (2 * K + 1)
    value_bound = first / (1 - W)
    first_d = K * W ** (K - 1) / (2 * K + 1)
    ratio_d = mp.mpf(K + 1) / K * W
    derivative_bound = first_d / (1 - ratio_d)
    return add_series_remainder(result, argument, value_bound, derivative_bound)


def soft_jets(q_box, y_box, zm_box):
    q = FirstJet.variable(q_box, 0)
    y = FirstJet.variable(y_box, 1)
    zm = FirstJet.variable(zm_box, 2)
    H = 2 * q / (1 + q) ** 2
    A = first_log(H) / first_log(q)
    C = factorial_series(y, "C")
    S = factorial_series(y, "S")
    b = q * S / (1 - q * C)
    w = y * b * b
    T = atanhc_series(w)
    divided_plus = A - 1 + 2 * A * b * T
    d = FirstJet.constant(iv.log(2)) - 2 * first_log(1 + q)
    minus = A * first_log((zm - q * q) / (zm - 1)) - first_log(zm) - d
    h = 2 / (1 + q) ** 2
    k = 2 * q * q / (1 + q) ** 2
    length = h * zm + k / zm - 2 * H * C
    return divided_plus, minus, length, w


def point_A(q):
    return mp.log(2 * q / (1 + q) ** 2) / mp.log(q)


def point_plus_divided(q, y):
    A = point_A(q)
    if y == 0:
        return A * (1 + q) / (1 - q) - 1
    x = mp.sqrt(y)
    return (
        A
        - 1
        + A
        * (mp.log(1 - q * mp.exp(-x)) - mp.log(1 - q * mp.exp(x)))
        / x
    )


def point_soft_roots(q):
    f0 = point_plus_divided(q, mp.mpf(0))
    if abs(f0) < mp.mpf("1e-70"):
        y = mp.mpf(0)
    else:
        top = (-mp.log(q) * (1 - mp.mpf("1e-30"))) ** 2
        y = bisect(lambda yy: point_plus_divided(q, yy), mp.mpf(0), top)
    return y, point_minus_root_q(q)


def point_minus_root_q(q):
    A = point_A(q)
    d = LN2 - 2 * mp.log(1 + q)
    gm = lambda z: A * mp.log((z - q * q) / (z - 1)) - mp.log(z) - d
    return bisect(gm, 1 + mp.mpf("1e-70"), 3)


def soft_boxes(qlo, qhi, last=False):
    if not last:
        sample_q = [qlo, (qlo + qhi) / 2, qhi]
        samples = [point_soft_roots(q) for q in sample_q]
        ys = [x[0] for x in samples]
        zs = [x[1] for x in samples]
    else:
        safe_hi = Q_SOFT_CENTER - Q_SOFT_RADIUS
        y_samples = [point_soft_roots(q)[0] for q in (qlo, (qlo + safe_hi) / 2)]
        ys = y_samples
        zs = [point_minus_root_q(q) for q in (qlo, (qlo + qhi) / 2, qhi)]
    width = qhi - qlo
    y_pad = max(mp.mpf("1e-50"), 120 * width)
    z_pad = max(mp.mpf("1e-50"), 8 * width)
    ylo = mp.mpf(0) if last else max(mp.mpf(0), min(ys) - y_pad)
    return I(ylo, max(ys) + y_pad), I(min(zs) - z_pad, max(zs) + z_pad)


def certify_soft_box(qlo, qhi, last=False):
    q_box = I(qlo, qhi)
    y_box, zm_box = soft_boxes(qlo, qhi, last)
    divided, gm, length, w = soft_jets(q_box, y_box, zm_box)
    divided_lo = soft_jets(q_box, I(lower(y_box)), zm_box)[0].value
    divided_hi = soft_jets(q_box, I(upper(y_box)), zm_box)[0].value
    gm_lo = soft_jets(q_box, y_box, I(lower(zm_box)))[1].value
    gm_hi = soft_jets(q_box, y_box, I(upper(zm_box)))[1].value
    roots_ok = (
        positive(divided.gradient[1])
        and positive(divided_hi)
        and (last or negative(divided_lo))
        and positive(gm_lo)
        and negative(gm_hi)
        and negative(gm.gradient[2])
        and upper(w.value) < mp.mpf("0.03")
    )
    if not roots_ok:
        return False, None, (y_box, zm_box)
    y_q = -divided.gradient[0] / divided.gradient[1]
    zm_q = -gm.gradient[0] / gm.gradient[2]
    length_q = (
        length.gradient[0]
        + length.gradient[1] * y_q
        + length.gradient[2] * zm_q
    )
    return positive(length_q), length_q, (y_box, zm_box)


def recursive_soft(a, b, depth=0):
    try:
        ok, derivative, _ = certify_soft_box(a, b, False)
    except (ValueError, ZeroDivisionError, mp.libmp.libmpf.ComplexResult):
        ok, derivative = False, None
    if ok:
        return [(a, b, derivative)]
    if depth >= 24:
        raise RuntimeError(f"soft subdivision failed on [{a}, {b}]")
    mid = (a + b) / 2
    return recursive_soft(a, mid, depth + 1) + recursive_soft(mid, b, depth + 1)


def soft_endpoint_certificate():
    qlo = Q_SOFT_CENTER - Q_SOFT_RADIUS
    qhi = Q_SOFT_CENTER + Q_SOFT_RADIUS

    def f(q):
        d = iv.log(2) - 2 * iv.log(1 + q)
        return (1 + q) * d + 2 * q * iv.log(q)

    f_lo, f_hi = f(I(qlo)), f(I(qhi))
    q_domain = I(mp.mpf(".1"), Q_GEOM)
    d = iv.log(2) - 2 * iv.log(1 + q_domain)
    f_prime = d + 2 * iv.log(q_domain)
    isolated = positive(f_lo) and negative(f_hi) and negative(f_prime)

    # The last box may extend by 1e-48 beyond q_soft.  For every admissible
    # q in it, D(q,0)<=0; D_y>0 and D(q,y_hi)>0 therefore enclose the root.
    last_lo = Q_SOFT_CENTER - mp.mpf("1e-5")
    last_ok, last_derivative, last_boxes = certify_soft_box(last_lo, qhi, True)
    return isolated and last_ok, (qlo, qhi), last_derivative, last_boxes


def stationary_enclosure():
    """Use strict local convexity and opposite endpoint derivatives."""
    local_radius = mp.mpf("0.005")
    left = R_STAR_CENTER - local_radius
    right = R_STAR_CENTER + local_radius
    convex = recursive_bulk(left, right, None, True)

    # A narrow rational enclosure of the unique derivative zero.
    radius = mp.mpf("1e-30")
    rlo, rhi = R_STAR_CENTER - radius, R_STAR_CENTER + radius
    left_ok, left_d, _, _ = certify_bulk_box(rlo, rlo, -1, False)
    right_ok, right_d, _, _ = certify_bulk_box(rhi, rhi, 1, False)
    if not (left_ok and right_ok and all(positive(x[3]) for x in convex)):
        raise RuntimeError("stationary enclosure failed")

    # Enclose q_star and L_star on the narrow r box.
    q_box = iv.exp(-1 / I(rlo, rhi))
    box_ok, _, _, root_boxes = certify_bulk_first(rlo, rhi, None)
    if not box_ok:
        raise RuntimeError("narrow stationary branch enclosure failed")
    zp_box, zm_box = root_boxes
    _, _, length = bulk_jets(I(rlo, rhi), zp_box, zm_box)
    return (left, right), convex, (rlo, rhi), q_box, length.value, left_d, right_d


def main():
    tail_ok, tail_derivative, q_tail, qr_tail = tail_certificate()
    if not tail_ok:
        raise RuntimeError("q -> 0 tail certificate failed")

    (
        local_interval,
        convex_boxes,
        r_star_box,
        q_star_box,
        length_star,
        stationary_left_d,
        stationary_right_d,
    ) = stationary_enclosure()
    local_left, local_right = local_interval

    left_boxes = recursive_bulk(mp.mpf(".02"), local_left, -1)
    q_soft_switch = mp.mpf(".1")
    r_soft_switch = -1 / mp.log(q_soft_switch)
    right_boxes = recursive_bulk(local_right, r_soft_switch, 1)

    endpoint_ok, q_soft_box, endpoint_derivative, endpoint_root_boxes = (
        soft_endpoint_certificate()
    )
    if not endpoint_ok:
        raise RuntimeError("soft endpoint certificate failed")
    regular_soft_end = Q_SOFT_CENTER - mp.mpf("1e-5")
    soft_boxes_certified = recursive_soft(q_soft_switch, regular_soft_end)

    qlo, qhi = q_soft_box
    qs_iv = I(qlo, qhi)
    A_soft = iv.log(2 * qs_iv / (1 + qs_iv) ** 2) / iv.log(qs_iv)
    s_soft = (1 - qs_iv) / (1 + qs_iv)

    print("ONE-CUT GLOBAL INTERVAL CERTIFICATE: PASS")
    print("scope=zero-slack terminal one-cut family only")
    print("q_soft_box=", I(qlo, qhi))
    print("A_soft_box=", A_soft)
    print("soft_edge_s_box=", s_soft)
    print("soft_edge_A_equals_s_overlap=", not (upper(A_soft) < lower(s_soft) or upper(s_soft) < lower(A_soft)))
    print("q_tail_cut=", mp.nstr(q_tail, 18))
    print("q_tail_derivative_bound=", tail_derivative)
    print("q_tail_qr_bound=", mp.nstr(qr_tail, 18))
    print("bulk_left_boxes=", len(left_boxes))
    print("local_convexity_boxes=", len(convex_boxes))
    print("bulk_right_boxes=", len(right_boxes))
    print("soft_regular_boxes=", len(soft_boxes_certified))
    print("soft_endpoint_derivative_bound=", endpoint_derivative)
    print("stationary_r_box=", I(*r_star_box))
    print("stationary_q_box=", q_star_box)
    print("stationary_left_derivative=", stationary_left_d)
    print("stationary_right_derivative=", stationary_right_d)
    print("minimum_length_box=", length_star)
    print("derivative_sign_pattern=negative,zero,positive")
    print("unique_global_minimum=PASS")


if __name__ == "__main__":
    main()
'''


# ============================================================================
# EMBEDDED SOURCE: verify_tao_sup_inequalities.py
# ============================================================================
SOURCES["verify_tao_sup_inequalities.py"] = r'''#!/usr/bin/env python3
"""Outward-interval checks for the three scalar inequalities in Tao's proof.

The expansive-rearrangement and duality parts of `tao_sup_1038.pdf` are
paper arguments.  That note leaves three elementary one-variable inequalities
as numerical verifications.  This script certifies them with `mpmath.iv` and
adaptive interval subdivision, and treats the unbounded tail analytically.
"""

from __future__ import annotations

from mpmath import iv, mp

if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


iv.prec = 110
mp.dps = 90

SQRT2_IV = iv.sqrt(iv.mpf(2))
TWO_SQRT2_IV = 2 * SQRT2_IV


def antiderivative_range(z):
    """Enclose f(z)=z-z log|z|, continuously extended by f(0)=0."""

    if z.a > 0 or z.b < 0:
        return z * (1 - iv.log(abs(z)))

    # On [0,h] with h<e, z(1-log z) is nonnegative and has maximum at
    # min(h,1).  The odd symmetry gives a safe enclosure even when the input
    # only touches zero at one endpoint.  Adaptive subdivision quickly makes
    # this symmetric enclosure sharp enough.
    h = abs(z).b
    assert h < 2
    if h <= 1:
        h_singleton = iv.mpf(h)
        magnitude = h_singleton * (1 - iv.log(h_singleton))
    else:
        magnitude = iv.mpf(1)
    return iv.mpf([-magnitude.b, magnitude.b])


def case1_difference(t):
    """Left minus right side of Tao's inequality (2.4)."""

    b = TWO_SQRT2_IV
    return (
        iv.log(1 / (t - 1)) * iv.log(1 / (b - t - 1))
        - iv.log(t + 1) * iv.log(b - t + 1)
    )


def case1_second_derivative(t):
    b = TWO_SQRT2_IV
    l1 = -iv.log(t - 1)
    l2 = -iv.log(b - t - 1)
    r1 = iv.log(t + 1)
    r2 = iv.log(b - t + 1)
    l1p = -1 / (t - 1)
    l2p = 1 / (b - t - 1)
    r1p = 1 / (t + 1)
    r2p = -1 / (b - t + 1)
    l1pp = 1 / (t - 1) ** 2
    l2pp = 1 / (b - t - 1) ** 2
    r1pp = -1 / (t + 1) ** 2
    r2pp = -1 / (b - t + 1) ** 2
    return (
        l1pp * l2 + 2 * l1p * l2p + l1 * l2pp
        - (r1pp * r2 + 2 * r1p * r2p + r1 * r2pp)
    )


def case2_potential(t):
    b = TWO_SQRT2_IV
    return -iv.log(t) + iv.mpf("0.7233") * (
        antiderivative_range(b - t)
        - antiderivative_range(iv.mpf("2.268742") - t)
    )


def case3_potential(t):
    b = TWO_SQRT2_IV
    return (
        -iv.log(t)
        + iv.mpf("0.192829")
        * (
            antiderivative_range(b - t)
            - antiderivative_range(iv.mpf("1.63") - t)
        )
        + iv.mpf("0.224")
        * (
            antiderivative_range(b - t)
            - antiderivative_range(iv.mpf("1.919") - t)
        )
        - iv.mpf("0.155") * iv.log(abs(b - t))
    )


def adaptive_negative(name, function, segments, minimum_width="1e-16"):
    """Prove function<0 on a finite union of closed real intervals."""

    min_width = mp.mpf(minimum_width)
    stack = [
        (mp.mpf(str(left)), mp.mpf(str(right)), 0)
        for left, right in segments
    ]
    boxes = 0
    max_depth = 0
    least_margin_box = None
    least_margin_upper = None

    while stack:
        left, right, depth = stack.pop()
        boxes += 1
        max_depth = max(max_depth, depth)
        value = function(iv.mpf([left, right]))
        if value.b < 0:
            if least_margin_upper is None or value.b > least_margin_upper:
                least_margin_upper = value.b
                least_margin_box = (left, right, value)
            continue
        if right - left <= min_width:
            raise AssertionError(
                f"{name}: failed to certify [{left}, {right}], value={value}"
            )
        middle = (left + right) / 2
        stack.append((left, middle, depth + 1))
        stack.append((middle, right, depth + 1))

    print(
        f"{name}: PASS boxes={boxes} max_depth={max_depth} "
        f"least_margin_box={least_margin_box}"
    )


def main():
    # Case 1 is even about t=sqrt(2), with value and first derivative zero
    # there.  Strict negativity immediately to the right follows from this
    # certified negative second derivative.
    center_lo = mp.mpf("1.414213562373095")
    center_hi = mp.mpf("1.414213562373096")
    near_right = mp.mpf("1.424213562373096")
    second = case1_second_derivative(iv.mpf([center_lo, near_right]))
    assert second.b < 0
    print("case1_near_center_second_derivative: PASS", second)
    adaptive_negative(
        "case1_remaining",
        case1_difference,
        # Deliberate overlaps at the human-readable case boundary avoid
        # making coverage depend on the last bit of an mp.mpf conversion.
        [(near_right, "1.762400000001")],
    )

    # `B_LO < 2sqrt(2) < B_HI`; the tiny bracket lets the continuous
    # antiderivative enclosure handle its zero without a singular evaluation.
    b_lo = "2.828427124746190"
    b_hi = "2.828427124746191"
    adaptive_negative(
        "case2_finite_range",
        case2_potential,
        [
            ("0.798699999999", "2.268742"),
            ("2.268742", b_lo),
            (b_lo, b_hi),
            (b_hi, "3.83"),
        ],
    )
    # For t >= 3.83 and s in [2.268742,2sqrt(2)], both t and t-s exceed one.
    # Every log(1/distance) term is then strictly negative.
    print("case2_unbounded_tail: PASS by distance>1")

    adaptive_negative(
        "case3",
        case3_potential,
        [
            ("0.762399999999", "1.63"),
            ("1.63", "1.919"),
            ("1.919", "2.798700000001"),
        ],
    )
    print("TAO SUPREMUM SCALAR CERTIFICATES: PASS")


if __name__ == "__main__":
    main()
'''


# ============================================================================
# EMBEDDED SOURCE: verify_low_k_mean_deficit_repair.py
# ============================================================================
SOURCES["verify_low_k_mean_deficit_repair.py"] = r'''#!/usr/bin/env python3
"""Exact-rational audit for low_k_mean_deficit_repair.md.

The analytic proof reduces its non-symbolic comparisons to the Fraction
identities checked here.  No floating-point arithmetic is used.
"""

from fractions import Fraction as F

if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


def main() -> None:
    K = F(29, 20)

    # exp(3/8) > its cubic Taylor partial sum > 29/20.
    x = F(3, 8)
    exp_partial = 1 + x + x**2 / 2 + x**3 / 6
    assert exp_partial == F(1489, 1024)
    assert exp_partial - K == F(21, 5120) > 0

    # The resulting lower bound for (K+1) K^{-K/(K+1)}.
    z = F(87, 392)
    exp_minus_lower = 1 - z + z**2 / 2 - z**3 / 6
    endpoint_mean_lower = F(49, 20) * exp_minus_lower
    assert endpoint_mean_lower - F(49, 25) == F(522631, 245862400) > 0

    # atanh-series lower bound for log 3.
    log3_lower = 2 * (F(1, 2) + F(1, 2) ** 3 / 3 + F(1, 2) ** 5 / 5)
    assert log3_lower == F(263, 240)

    # atanh-series upper bound for log 2, including its geometric tail.
    u = F(1, 3)
    log2_upper = 2 * (u + u**3 / 3) + 2 * u**5 / (5 * (1 - u**2))
    assert log2_upper == F(1123, 1620)

    log_margin_lower = log3_lower - K * log2_upper
    assert log_margin_lower == F(1469, 16200)
    assert log_margin_lower - F(9, 100) == F(11, 16200) > 0

    # e > 8/3 makes (6/25)/e < 9/100.
    e_lower = 1 + 1 + F(1, 2) + F(1, 6)
    assert e_lower == F(8, 3)
    assert F(6, 25) / e_lower == F(9, 100)

    # sqrt(2)>4/3, hence sqrt(2)+2/3>2.
    assert F(2) > F(4, 3) ** 2

    print("LOW-k MEAN-DEFICIT REPAIR: PASS")
    print("epsilon_K < 1/25: exact rational audit PASS")
    print("logarithmic scalar margin >", F(11, 16200))
    print("conclusion: sum_i R_i > 1/3 and J > 2")


if __name__ == "__main__":
    main()
'''


# ============================================================================
# EMBEDDED SOURCE: verify_negative_platform_affine_reference_basics.py
# ============================================================================
SOURCES["verify_negative_platform_affine_reference_basics.py"] = r'''#!/usr/bin/env python3
"""Outward checks of the affine negative-platform reference prerequisites.

This does not certify the mixed interval inequality.  It only proves, on
29/20 <= k <= 23/10 with a=1153/500-k/4, that the reference measure is
strictly positive, its platform constant is negative, and its right-side
weighted potential has a positive point.  Strict concavity then gives the
two separated right roots and fixes the main-crossing slope sign.
"""

from mpmath import iv

if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


iv.prec = 150

N = 1000


def main() -> None:
    k0 = iv.mpf(29) / 20
    span = iv.mpf(17) / 20
    test_x = iv.mpf(6) / 5

    min_density_slack = None
    max_platform = None
    min_test_potential = None

    for i in range(N):
        klo = k0 + span * i / N
        khi = k0 + span * (i + 1) / N
        k = iv.mpf([klo.a, khi.b])
        a = iv.mpf(1153) / 500 - k / 4

        # Positivity is equivalent to a >= 2(k/(k+1))^2.
        density_slack = a - 2 * (k / (k + 1)) ** 2
        assert density_slack.a > 0

        platform = iv.log((2 - a) / 4) + k * iv.log(
            (a + 2 + 2 * iv.sqrt(2 * a)) / 4
        )
        assert platform.b < 0

        # Stable hyperbolic coordinate for x=6/5<a.
        center = (a + 2) / 2
        radius = (2 - a) / 2
        z = (center - test_x) / radius
        assert z.a > 1
        rho = 1 / (z + iv.sqrt(z * z - 1))
        tau = (iv.sqrt(2) - iv.sqrt(a)) / (iv.sqrt(2) + iv.sqrt(a))
        potential = (
            k * iv.log(test_x)
            + iv.log(radius / (2 * rho))
            - 2 * k * iv.log(1 - tau * rho)
        )
        assert potential.a > 0

        if min_density_slack is None or density_slack.a < min_density_slack:
            min_density_slack = density_slack.a
        if max_platform is None or platform.b > max_platform:
            max_platform = platform.b
        if min_test_potential is None or potential.a < min_test_potential:
            min_test_potential = potential.a

    print("NEGATIVE-PLATFORM AFFINE REFERENCE BASIC CERTIFICATE")
    print("1000 outward k boxes: PASS")
    print("minimum density-edge slack:", min_density_slack)
    print("largest platform constant upper endpoint:", max_platform)
    print("minimum W_k,a(6/5) lower endpoint:", min_test_potential)
    print("strict reference positivity and main separation: PASS")
    print("PASS")


if __name__ == "__main__":
    main()
'''


# ============================================================================
# EMBEDDED SOURCE: verify_negative_platform_affine_uniform.py
# ============================================================================
SOURCES["verify_negative_platform_affine_uniform.py"] = r'''#!/usr/bin/env python3
"""Fail-closed negative-platform rectangle-scalar certificate.

This file is independent of ``verify_mixed_interval_derivative_signs.py``.
It covers exactly

    36/25 <= k <= 21/10,  a = 1153/500-k/4,
    21/10 <= k <= 21/5,   a = 9/5.

The circle--bathtub identity reduces every angular interval to a rectangle
in its two normalized masses Q,R.  Self-arc monotonicity and the nonnegative
Fourier-square identity reduce that rectangle further to explicit one-variable
scalars.  The affine range retains the n=1 square; on the constant range the
self-arc gaps alone suffice.  Crossings are enclosed uniformly on every k
slab by endpoint sign brackets, a strict W_x sign, and a certified implicit
derivative orientation.  Floating-point roots only propose the brackets.

The program prints PASS only if every parameter and scalar box is exhausted.
The terminal reference for k>=21/5 is certified in a separate verifier.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import sys

import mpmath as mp
from flint import arb, ctx


if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


ctx.prec = 160
mp.mp.dps = 70

# Start below 29/20.  The overlap [36/25,29/20] makes the global cover
# insensitive to the last-bit representation of a decimal/rational endpoint.
K_LO = mp.mpf(36) / 25
K_AFF_HI = mp.mpf(21) / 10
K_CONST_HI = mp.mpf(21) / 5
LSTAR_LO = mp.mpf("1.83443047576266171109075363512055343651186425665")
LSTAR_HI = mp.mpf("1.83443047576266171109075363512901884952989750747")
PI = mp.pi


def B(lo, hi=None):
    return core.B(lo, hi)


def lower(x):
    return core.lo(x)


def upper(x):
    return core.hi(x)


def err(radius):
    return core.symmetric_error(radius)


def reference_a(k, kind):
    if kind == "affine":
        return arb(1153) / 500 - k / 4
    if kind == "constant":
        return arb(9) / 5
    raise ValueError(kind)


def external_quantities(k, x, kind):
    """Return W,W_x and the auxiliary quantities, all as Arb expressions."""
    a = reference_a(k, kind)
    c = (a + 2) / 2
    radius = (2 - a) / 2
    K0 = (2 * a).sqrt()
    # Stable forms avoid cancellation when the conductor is short.
    rho0 = (arb(2).sqrt() - a.sqrt()) / (arb(2).sqrt() + a.sqrt())
    Kx = ((a - x) * (2 - x)).sqrt()
    rhox = radius / (c - x + Kx)
    W = (k * abs(x).log() + ((c - x + Kx) / 2).log()
         - 2 * k * (1 - rho0 * rhox).log())
    Wx = (k / x - 1 / Kx
          + 2 * k * rho0 * rhox / (Kx * (1 - rho0 * rhox)))
    return W, Wx, a, c, radius, rho0, Kx, rhox


@dataclass
class Dual:
    value: object
    derivative: object

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Dual) else Dual(x, arb(0))

    def __add__(self, other):
        other = self.coerce(other)
        return Dual(self.value + other.value, self.derivative + other.derivative)

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.value, -self.derivative)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Dual(self.value * other.value,
                    self.derivative * other.value + self.value * other.derivative)

    __rmul__ = __mul__

    def reciprocal(self):
        return Dual(1 / self.value, -self.derivative / self.value**2)

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()

    def __pow__(self, n):
        assert n == 2
        return self * self

    def sqrt(self):
        root = self.value.sqrt()
        return Dual(root, self.derivative / (2 * root))

    def log(self):
        return Dual(self.value.log(), self.derivative / self.value)

    def __abs__(self):
        if lower(self.value) > 0:
            return self
        if upper(self.value) < 0:
            return -self
        raise ValueError("absolute value crosses zero")


def external_W_dual(k, x, kind):
    a = (Dual(arb(1153) / 500, arb(0)) - k / 4
         if kind == "affine" else Dual(arb(9) / 5, arb(0)))
    c = (a + 2) / 2
    radius = (2 - a) / 2
    sqrt2 = arb(2).sqrt()
    rho0 = (sqrt2 - a.sqrt()) / (sqrt2 + a.sqrt())
    Kx = ((a - x) * (2 - x)).sqrt()
    rhox = radius / (c - x + Kx)
    return (k * abs(x).log() + ((c - x + Kx) / 2).log()
            - 2 * k * (1 - rho0 * rhox).log())


_point_root_cache = {}


def point_roots(k, kind):
    key = kind, mp.nstr(k, 60)
    if key in _point_root_cache:
        return _point_root_cache[key]
    a = (mp.mpf(1153) / 500 - mp.mpf(k) / 4
         if kind == "affine" else mp.mpf(9) / 5)
    out = diagnostic.solve_crossings(k, a)
    _point_root_cache[key] = out
    return out


def root_bracket(klo, khi, minus, kind):
    """Uniform root box, using a certified implicit-derivative orientation."""
    rlo = point_roots(klo, kind)[0 if minus else 1]
    rhi = point_roots(khi, kind)[0 if minus else 1]
    pad = mp.mpf("1e-35")
    # Certify the two endpoint roots independently.
    for kp, root in ((klo, rlo), (khi, rhi)):
        kk = B(kp)
        wl = external_quantities(kk, B(root - pad), kind)[0]
        wr = external_quantities(kk, B(root + pad), kind)[0]
        if minus:
            assert lower(wl) > 0 and upper(wr) < 0
        else:
            assert upper(wl) < 0 and lower(wr) > 0

    left, right = min(rlo, rhi) - pad, max(rlo, rhi) + pad
    kb = B(klo, khi)
    xb = B(left, right)
    Wx = external_quantities(kb, xb, kind)[1]
    if minus:
        assert upper(Wx) < 0
    else:
        assert lower(Wx) > 0

    # Along the actual affine/constant parameter curve, x'=-W_k/W_x.
    kd = Dual(kb, arb(1))
    xd = Dual(xb, arb(0))
    Wk = external_W_dual(kd, xd, kind).derivative
    slope = -Wk / Wx
    observed = rhi - rlo
    if observed > 0:
        assert lower(slope) > 0
    elif observed < 0:
        assert upper(slope) < 0
    else:
        assert False
    return xb


@dataclass
class AffineBox:
    klo: mp.mpf
    khi: mp.mpf
    family: core.Family
    cn: arb                    # C_eff/a_pi in normalized coordinates
    eta_total: arb             # physical eta mass (audit: contains 1)
    xi_total: arb
    xminus: arb
    xplus: arb
    api: arb
    bpi: arb
    Ceff: arb
    Qmax: arb
    Rmax: arb
    H: arb


_family_cache = {}


def affine_family_box(klo, khi, kind="affine"):
    key = kind, mp.nstr(klo, 40), mp.nstr(khi, 40)
    if key in _family_cache:
        return _family_cache[key]
    kb = B(klo, khi)
    xm = root_bracket(klo, khi, True, kind)
    xp = root_bracket(klo, khi, False, kind)
    Wm, Wxm, a, c, radius, rho0, Km, rm = external_quantities(kb, xm, kind)
    Wp, Wxp, _, _, _, _, Kp, rp = external_quantities(kb, xp, kind)
    assert upper(Wxm) < 0 and lower(Wxp) > 0
    sm, sp = -1 / Wxm, 1 / Wxp

    # The endpoint values and total xi mass are most stably written in the
    # Poisson parameters.  D=sigma P_rho(0), hence R0=D-sigma_- -sigma_+.
    bm_pi = 4 * sm * rm / (1 - rm**2)
    bp_pi = 4 * sp * rp / (1 - rp**2)
    bpi = bm_pi + bp_pi
    lam = bp_pi / bpi
    # Cancellation-free total mass: P_rho(0)-1=2rho/(1-rho).
    R0 = 2 * sm * rm / (1 - rm) + 2 * sp * rp / (1 - rp)
    api = 1 + 2 * kb * rho0 / (1 + rho0)
    H = radius / 2
    C = H.log() + kb * ((a + 2 + 2 * (2 * a).sqrt()) / 4).log()
    M0 = xp - xm
    target = B(LSTAR_LO, LSTAR_HI)
    Ceff = C + (target - M0) / R0
    cn = Ceff / api
    fam = core.Family(rho0, H, kb / api, lam, rp, rm,
                      (api * bpi).log())

    # Structural audits needed by the circle lemma and Fourier tails.
    assert lower(rho0) > 0 and upper(rho0) < 1
    assert lower(rp) > 0 and upper(rp) < 1
    assert lower(rm) > 0 and upper(rm) < 1
    # bm_pi,bp_pi are strictly positive, so their exact ratio lies in (0,1).
    # Direct ball division may extend slightly past 1 because it forgets the
    # common denominator; no later scalar uses that loose ratio.
    assert lower(bm_pi) > 0 and lower(bp_pi) > 0
    assert upper(cn) < 0
    # eta(0)>0 proves eta positivity; xi positivity follows termwise from
    # sigma_±>0 and P_rho(0)-P_rho(theta)>=0.
    eta_left = 1 - 2 * kb * rho0 / (1 - rho0)
    assert lower(eta_left) > 0
    eta_total = B(1)

    Qmax = arb.pi() / api
    Rmax = arb.pi() * R0 / bpi
    assert lower(Rmax) > 0 and upper(Rmax) < lower(Qmax)
    assert upper(Qmax) < PI
    out = AffineBox(klo, khi, fam, cn, eta_total, R0, xm, xp,
                    api, bpi, Ceff, Qmax, Rmax, H)
    _family_cache[key] = out
    return out


def square_ball(x):
    """Tight square of a real Arb ball (ordinary ball multiplication is loose)."""
    xlo, xhi = lower(x), upper(x)
    top = max(xlo*xlo, xhi*xhi)
    bottom = mp.mpf(0) if xlo <= 0 <= xhi else min(xlo*xlo, xhi*xhi)
    return B(bottom, top)


def h_gap(q, N=80):
    """Outward h(q)=A(q,q)-log(q/pi), using a positive Fourier sum."""
    assert lower(q) > 0 and upper(q) < PI
    total = arb(0)
    for n in range(1, N + 1):
        total += square_ball((n * q).sin()) / (n**3)
    qmin = lower(q)
    # 0 <= sum_{n>N} sin^2(nq)/n^3 <= 1/(2N^2).
    # Compute the tail cap outward as well; an ordinary mp division here
    # would only be a high-precision approximation to the required cap.
    tail_ball = arb(1) / (2 * N**2 * B(qmin)**2)
    tail_upper = upper(tail_ball)
    Aself = -total / q**2 + B(-tail_upper, 0)
    return Aself - (q / arb.pi()).log()


def sinc(q):
    return q.sin() / q


def sinc_prime(q):
    return (q * q.cos() - q.sin()) / q**2


def scalar_base(box):
    """B=L0+h(Qmax)+h(Rmax) in the retained-square lower bound."""
    # h is decreasing.  Evaluating at the outward upper endpoints avoids
    # injecting the parameter-ball radius through hundreds of trigonometric
    # terms, while remaining a rigorous lower bound.
    hq = h_gap(B(upper(box.Qmax)))
    hr = h_gap(B(upper(box.Rmax)))
    return ((2 * box.H / (box.api * box.bpi)).log()
            + hq + hr)


def certify_affine_scalar_slab(klo, khi, qcells=32):
    """Retain the n=1 square and prove its Q scalar decreases to Qmax."""
    box = affine_family_box(klo, khi, "affine")
    base = scalar_base(box)
    P = -box.Ceff * arb.pi() / box.api
    assert lower(P) > 0

    # If Q<=Rmax the n=1 square can vanish, but P/Q>=P/Rmax.
    left = base + P / box.Rmax
    if lower(left) <= 0:
        return False, ("Q<=Rmax", left)

    # For Rmax<=Q<=Qmax the closest permissible sinc(R) is sinc(Rmax).
    # Certify f'(Q)<0 after the affine chart Q=R+u(Qmax-R).
    for j in range(qcells):
        u = B(mp.mpf(j) / qcells, mp.mpf(j + 1) / qcells)
        Q = box.Rmax + u * (box.Qmax - box.Rmax)
        deriv = (-P / Q**2
                 + 2 * (sinc(Q) - sinc(box.Rmax)) * sinc_prime(Q))
        if upper(deriv) >= 0:
            return False, ("Q derivative", j, deriv, Q)

    delta = sinc(box.Qmax) - sinc(box.Rmax)
    corner = base + P / box.Qmax + square_ball(delta)
    if lower(corner) <= 0:
        return False, ("corner", corner)
    return True, (left, corner)


def certify_constant_scalar_slab(klo, khi):
    """The self-arc gaps alone suffice for a=9/5 once k>=21/10."""
    box = affine_family_box(klo, khi, "constant")
    base = scalar_base(box)
    P = -box.Ceff * arb.pi() / box.api
    assert lower(P) > 0
    # h is decreasing, and P/Q is decreasing.  Their rectangle minimum is
    # at Qmax,Rmax; the nonnegative Fourier-square sum is discarded.
    scalar = base + P / box.Qmax
    if lower(scalar) <= 0:
        return False, scalar
    return True, scalar


def main():
    step = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf(".0025")
    k = K_LO
    slabs = 0
    worst = mp.inf
    while k < K_AFF_HI:
        kh = k + step
        if kh >= K_AFF_HI or K_AFF_HI - kh < mp.mpf("1e-40"):
            kh = K_AFF_HI
        ok, report = certify_affine_scalar_slab(k, kh)
        if not ok:
            print("UNRESOLVED: affine scalar", k, kh, report)
            return 1
        slabs += 1
        worst = min(worst, lower(report[0]), lower(report[1]))
        if slabs % 40 == 0:
            print("affine progress", mp.nstr(kh, 8), flush=True)
        k = kh

    const_slabs = 0
    k = K_AFF_HI
    while k < K_CONST_HI:
        kh = k + step
        if kh >= K_CONST_HI or K_CONST_HI - kh < mp.mpf("1e-40"):
            kh = K_CONST_HI
        ok, scalar = certify_constant_scalar_slab(k, kh)
        if not ok:
            print("UNRESOLVED: constant scalar", k, kh, scalar)
            return 1
        const_slabs += 1
        worst = min(worst, lower(scalar))
        if const_slabs % 100 == 0:
            print("constant progress", mp.nstr(kh, 8), flush=True)
        k = kh
    print("PASS: negative-platform rectangle scalar cover")
    print("affine slabs =", slabs, "constant slabs =", const_slabs)
    print("minimum certified scalar lower bound =", worst)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''


# ============================================================================
# EMBEDDED SOURCE: verify_negative_platform_terminal_refined_scalar.py
# ============================================================================
SOURCES["verify_negative_platform_terminal_refined_scalar.py"] = r'''#!/usr/bin/env python3
"""Refined terminal circle-scalar certificate down to k=21/5.

For q <= 26631/10^6 the simpler certificate
``verify_negative_platform_terminal_scalar.py`` applies.  On the short
remaining terminal strip this verifier retains the two sharp self-arc gaps

    h(Q) = A(Q,Q)-log(Q/pi),

and uses the total-mass caps Q<=pi/a_pi and R<=pi*R0/b_pi.  Since h is
decreasing, only outward upper bounds for those two caps are required.
"""

from __future__ import annotations

import mpmath as mp
from mpmath import iv
from flint import arb, acb, ctx


if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


mp.mp.dps = 90
iv.dps = 90
ctx.prec = 200

K_CUT = mp.mpf(21) / 5
Q_SPLIT_NUM = 26631
Q_SPLIT_DEN = 10**6
Q_CAP_NUM = 41542
Q_CAP_DEN = 10**6
R_STEP = mp.mpf(".002")


def h_point_lower(x):
    """Outward point value of h(x), for an already outward upper cap x."""
    x = core.B(x)
    z = acb(0, 2 * x).exp()
    c3 = z.polylog(3).real
    value = -(arb(3).zeta() - c3) / (2 * x * x) - (x / arb.pi()).log()
    return core.lo(value), value


def slab_data(r_box, zp, zm):
    """Stable D, Qmax, Rmax, eta(0), and slope denominators."""
    q = iv.exp(-1 / r_box)
    d = iv.log(2) - 2 * iv.log(1 + q)
    rd = r_box * d
    A = 1 - rd
    P = rd + 2 * q * (1 - rd) / (1 + q)  # a_pi*r*d

    def raw(z):
        return 1 - A * (1 - q * q) * z / ((1 - z) * (z - q * q))

    rawp, rawm = raw(zp), raw(zm)
    wp, wm = -1 / rawp, 1 / rawm
    denominator = 2 * P * (wp + wm)

    # Total normalized eta mass is 1/a_pi=(r*d)/P.
    qmax = iv.pi * rd / P

    # R0/bpi after cancelling 2*r*d*H from numerator and denominator.
    rhop, rhom = q / zp, q / zm
    rratio = ((1 + rhop) * wp + (1 + rhom) * wm) / (2 * (wp + wm))
    rmax = iv.pi * rratio

    k = (1 - rd) / rd
    eta_zero = 1 - 2 * k * q / (1 - q)
    return denominator, qmax, rmax, eta_zero, rawp, rawm


def main():
    qsplit = iv.mpf(Q_SPLIT_NUM) / Q_SPLIT_DEN
    qcap = iv.mpf(Q_CAP_NUM) / Q_CAP_DEN
    dcap = iv.log(2) - 2 * iv.log(1 + qcap)
    kcap = -iv.log(qcap) / dcap - 1
    assert onecut.upper(kcap) < K_CUT

    # The same monotonic map audit as in the simple terminal certificate.
    gcap = (1 + qcap) * dcap + 2 * qcap * iv.log(qcap)
    gprime_cap = iv.log(2 * qcap**2 / (1 + qcap) ** 2)
    assert onecut.lower(gcap) > 0 and onecut.upper(gprime_cap) < 0

    rsplit = -1 / iv.log(qsplit)
    rcap = -1 / iv.log(qcap)
    r = onecut.lower(rsplit)
    rend = onecut.upper(rcap)
    slabs = 0
    worst = mp.inf
    worst_report = None

    while r < rend:
        right = min(rend, r + R_STEP)
        roots_ok, _, _, roots = onecut.certify_bulk_first(r, right, None)
        assert roots_ok, (r, right, roots)
        zp, zm = roots
        denominator, qmax, rmax, eta0, rawp, rawm = slab_data(
            onecut.I(r, right), zp, zm
        )
        assert onecut.upper(rawp) < 0 and onecut.lower(rawm) > 0
        assert onecut.lower(eta0) > 0

        q_upper = onecut.upper(qmax)
        r_upper = onecut.upper(rmax)
        assert 0 < q_upper < mp.pi and 0 < r_upper < mp.pi
        hq_lower, hq_box = h_point_lower(q_upper)
        hr_lower, hr_box = h_point_lower(r_upper)
        # All three terms stay in Arb.  In particular, do not turn the
        # outward denominator endpoint into an ordinary mp.log value.
        denominator_upper = onecut.upper(denominator)
        scalar_box = -core.B(denominator_upper).log() + hq_box + hr_box
        scalar = core.lo(scalar_box)
        assert scalar > 0, (r, right, denominator, qmax, rmax,
                            hq_box, hr_box, scalar_box)
        if scalar < worst:
            worst = scalar
            worst_report = (r, right, denominator, qmax, rmax,
                            hq_box, hr_box, scalar_box)
        slabs += 1
        r = right

    print("REFINED TERMINAL CIRCLE-SCALAR CERTIFICATE: PASS")
    print("q strip =", qsplit, qcap)
    print("k(q cap) =", kcap)
    print("refined r slabs =", slabs)
    print("minimum slab lower bound =", worst)
    print("worst slab data =", worst_report)
    print("q <= 26631/10^6: covered by the simple terminal certificate")
    print("all k >= 21/5: PASS")


if __name__ == "__main__":
    main()
'''


# ============================================================================
# EMBEDDED SOURCE: verify_negative_platform_terminal_scalar.py
# ============================================================================
SOURCES["verify_negative_platform_terminal_scalar.py"] = r'''#!/usr/bin/env python3
"""Outward terminal zero-platform circle-scalar certificate.

This covers every ``k >= 233/50`` by the zero-platform one-cut reference.
The global one-cut minimum ``M0 >= LSTAR`` is the already independent
certificate in ``verify_onecut_global.py``.  Here we certify the remaining
facts: the k-to-q map, positivity and separated crossings, monotonicity of
the endpoint scalar, and its strictly positive worst endpoint.

The stable variables are

    r = -1/log(q),       z_plus = q*u_plus,       z_minus = q*u_minus.

No floating-point root is trusted: point roots only propose brackets, while
uniform interval endpoint signs and strict root derivatives certify them.
"""

from __future__ import annotations

import mpmath as mp
from mpmath import iv


if not __debug__:
    raise RuntimeError("certificate checks require Python without -O")


mp.mp.dps = 90
iv.dps = 90

K_CUT = mp.mpf(233) / 50
Q_CAP_NUM = 26631
Q_CAP_DEN = 10**6
R_TAIL = mp.mpf(".02")
R_STEP = mp.mpf(".01")


def scalar_jet(r_box, zp_box, zm_box):
    """Return D, D_r, eta(0), and the two slope denominators.

    The circle scalar without the favorable effective-platform correction is

        log(2H/(a_pi*b_pi)) = -log(D).

    All q-small factors have been cancelled algebraically before evaluation.
    """
    r = onecut.Jet.variable(r_box, 0)
    zp = onecut.Jet.variable(zp_box, 1)
    zm = onecut.Jet.variable(zm_box, 2)
    q = onecut.jexp(-1 / r)
    d = onecut.Jet.constant(iv.log(2)) - 2 * onecut.jlog(1 + q)
    rd = r * d
    A = 1 - rd

    # (a_pi*r*d) in a form regular as q -> 0.  Here
    # k=A/(r*d) and a_pi=1+2kq/(1+q).
    P = rd + 2 * q * (1 - rd) / (1 + q)

    def raw(z):
        return 1 - A * (1 - q * q) * z / ((1 - z) * (z - q * q))

    rawp, rawm = raw(zp), raw(zm)
    denominator = 2 * P * (-1 / rawp + 1 / rawm)

    gp, gm, _ = onecut.bulk_jets(r_box, zp_box, zm_box)
    zp_r = -gp.gradient[0] / gp.gradient[1]
    zm_r = -gm.gradient[0] / gm.gradient[2]
    denominator_r = (
        denominator.gradient[0]
        + denominator.gradient[1] * zp_r
        + denominator.gradient[2] * zm_r
    )

    k = (1 - rd) / rd
    eta_zero = 1 - 2 * k * q / (1 - q)
    return denominator.value, denominator_r, eta_zero.value, rawp.value, rawm.value


def scalar_value(r_box, zp_box, zm_box):
    """Zeroth-order counterpart used at the endpoint and in the tail."""
    q = iv.exp(-1 / r_box)
    d = iv.log(2) - 2 * iv.log(1 + q)
    rd = r_box * d
    A = 1 - rd
    P = rd + 2 * q * (1 - rd) / (1 + q)

    def raw(z):
        return 1 - A * (1 - q * q) * z / ((1 - z) * (z - q * q))

    rawp, rawm = raw(zp_box), raw(zm_box)
    denominator = 2 * P * (-1 / rawp + 1 / rawm)
    return denominator, rawp, rawm


def tail_value():
    """Regular enclosure on 0 <= r <= .02 without dividing by r."""
    q0 = mp.exp(-1 / R_TAIL)
    r = onecut.I(0, R_TAIL)
    q = onecut.I(0, q0)
    d = iv.log(2) - 2 * iv.log(1 + q)
    rd = r * d
    A = 1 - rd
    P = rd + 2 * q * (1 - rd) / (1 + q)
    zp = onecut.I(mp.mpf(".499"), mp.mpf(".501"))
    zm = onecut.I(mp.mpf("1.49"), mp.mpf("1.5001"))

    def raw(z):
        return 1 - A * (1 - q * q) * z / ((1 - z) * (z - q * q))

    rawp, rawm = raw(zp), raw(zm)
    denominator = 2 * P * (-1 / rawp + 1 / rawm)

    # For r<=.02, q/r is increasing.  This gives a nonsingular positivity
    # check for the left endpoint of the eta density.
    dmin = onecut.lower(d)
    kq_upper = q0 / (R_TAIL * dmin)
    eta_zero_lower = 1 - 2 * kq_upper / (1 - q0)
    return denominator, rawp, rawm, eta_zero_lower


def main():
    qcap = iv.mpf(Q_CAP_NUM) / Q_CAP_DEN
    dcap = iv.log(2) - 2 * iv.log(1 + qcap)
    kcap = -iv.log(qcap) / dcap - 1
    assert onecut.upper(kcap) < K_CUT

    # k'(q)<0 is equivalent to g(q)>0, where g decreases on this range.
    # Its endpoint sign therefore certifies the full map (0,qcap].
    gcap = (1 + qcap) * dcap + 2 * qcap * iv.log(qcap)
    gprime_cap = iv.log(2 * qcap**2 / (1 + qcap) ** 2)
    assert onecut.lower(gcap) > 0 and onecut.upper(gprime_cap) < 0

    # The q->0 chart certifies both root branches by endpoint signs and
    # strict z derivatives.  It also supplies a very coarse scalar bound.
    tail_ok, _, _, _ = onecut.tail_certificate()
    assert tail_ok
    dtail, rawp_tail, rawm_tail, eta0_tail = tail_value()
    assert onecut.upper(rawp_tail) < 0 and onecut.lower(rawm_tail) > 0
    assert eta0_tail > 0

    rcap_iv = -1 / iv.log(qcap)
    rcap_lo, rcap_hi = onecut.bounds(rcap_iv)

    r = R_TAIL
    slabs = 0
    minimum_derivative = mp.inf
    minimum_eta_zero = mp.inf
    while r < rcap_hi:
        right = min(rcap_hi, r + R_STEP)
        roots_ok, _, _, roots = onecut.certify_bulk_first(r, right, None)
        assert roots_ok, (r, right, roots)
        zp, zm = roots
        value, derivative, eta_zero, rawp, rawm = scalar_jet(
            onecut.I(r, right), zp, zm
        )
        assert onecut.upper(rawp) < 0 and onecut.lower(rawm) > 0
        assert onecut.lower(derivative) > 0
        assert onecut.lower(eta_zero) > 0
        minimum_derivative = min(minimum_derivative, onecut.lower(derivative))
        minimum_eta_zero = min(minimum_eta_zero, onecut.lower(eta_zero))
        slabs += 1
        r = right

    # Evaluate the increasing denominator on the outward endpoint r-box.
    endpoint_ok, _, _, endpoint_roots = onecut.certify_bulk_first(
        rcap_lo, rcap_hi, None
    )
    assert endpoint_ok
    dend, rawp_end, rawm_end = scalar_value(rcap_iv, *endpoint_roots)
    assert onecut.upper(rawp_end) < 0 and onecut.lower(rawm_end) > 0
    assert onecut.upper(dtail) < onecut.upper(dend)
    # The exact sign is already equivalent to the outward endpoint being
    # below one.  Keep the displayed logarithmic bound interval-valued too.
    assert onecut.upper(dend) < 1
    scalar_box = -iv.log(onecut.I(onecut.upper(dend)))
    scalar_lower = onecut.lower(scalar_box)
    assert scalar_lower > 0

    print("TERMINAL ZERO-PLATFORM CIRCLE-SCALAR CERTIFICATE: PASS")
    print("q cap =", qcap)
    print("k(q cap) =", kcap)
    print("strict k(q) decrease on (0,q cap]: PASS")
    print("tail crossing/slope/eta signs: PASS")
    print("bulk r slabs =", slabs)
    print("minimum denominator derivative lower bound =", minimum_derivative)
    print("minimum bulk eta(0) lower bound =", minimum_eta_zero)
    print("endpoint denominator =", dend)
    print("global simple circle-scalar lower bound =", scalar_box)
    print("C_eff <= 0: PASS (by the independent one-cut global minimum certificate)")
    print("all k >= 233/50: PASS")


if __name__ == "__main__":
    main()
'''


# ============================================================================
# SINGLE-FILE LOADER AND FAIL-CLOSED MASTER DRIVER
# ============================================================================

_LOADED: dict[str, types.ModuleType] = {}


def _module_name(filename: str) -> str:
    if not filename.endswith(".py"):
        raise ValueError(filename)
    return filename[:-3]


def _load_embedded_module(filename: str) -> types.ModuleType:
    """Compile one readable source section and inject its embedded dependencies."""
    cached = _LOADED.get(filename)
    if cached is not None:
        return cached
    if filename not in SOURCES:
        raise KeyError(f"unknown embedded module: {filename}")

    injected: dict[str, types.ModuleType] = {}
    for alias, dependency in DEPENDENCY_ALIASES.get(filename, {}).items():
        injected[alias] = _load_embedded_module(dependency)

    name = _module_name(filename)
    module = types.ModuleType(name)
    module.__file__ = f"<embedded:{filename}>"
    module.__package__ = ""
    module.__dict__.update(injected)
    _LOADED[filename] = module
    # Register before exec so dataclasses and any standard import machinery can
    # resolve cls.__module__.  Same-named ambient modules are never trusted.
    sys.modules[name] = module
    try:
        code = compile(SOURCES[filename], module.__file__, "exec")
        exec(code, module.__dict__)
    except BaseException:
        _LOADED.pop(filename, None)
        if sys.modules.get(name) is module:
            sys.modules.pop(name, None)
        raise
    return module


def _run_embedded_certificate(filename: str) -> int:
    if not __debug__ or sys.flags.optimize:
        print("FAIL: the certificate suite must not be run with Python -O")
        return 2
    module = _load_embedded_module(filename)
    entry = getattr(module, "main", None)
    if not callable(entry):
        print(f"FAIL: embedded certificate has no callable main(): {filename}")
        return 2

    # Original children received no positional arguments.  Hide this wrapper's
    # private dispatch arguments; one child accepts an optional numeric argv[1].
    old_argv = sys.argv
    sys.argv = [filename]
    try:
        result = entry()
    finally:
        sys.argv = old_argv
    return 0 if result is None else int(result)


def _run_master() -> int:
    if not __debug__ or sys.flags.optimize:
        print("FAIL: the certificate suite must not be run with Python -O")
        return 2

    expected = {
        *CERTIFICATES,
        "negative_platform_fourier.py",
        "verify_mixed_interval_derivative_signs.py",
    }
    if set(SOURCES) != expected:
        print("FAIL: embedded certificate source set is incomplete")
        return 2

    env = dict(os.environ)
    # Several children deliberately use assert as a fail-closed check.
    env.pop("PYTHONOPTIMIZE", None)
    env["OPENBLAS_NUM_THREADS"] = "1"
    script = str(Path(__file__).resolve())

    for filename in CERTIFICATES:
        print(f"\n=== {filename} ===", flush=True)
        result = subprocess.run(
            [sys.executable, "-B", script, "--certificate", filename],
            cwd=Path(__file__).resolve().parent,
            env=env,
            check=False,
        )
        if result.returncode:
            print(f"FAIL: {filename} exited {result.returncode}")
            return result.returncode

    print("\nCOMPLETE ERDOS 1038 SELF-CONTAINED CERTIFICATE SUITE: PASS")
    return 0


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if len(args) == 2 and args[0] == "--certificate":
        if args[1] not in CERTIFICATES:
            print(f"FAIL: unknown certificate {args[1]!r}")
            return 2
        return _run_embedded_certificate(args[1])
    if args:
        print(f"usage: {Path(sys.argv[0]).name} [--certificate CERTIFICATE]")
        return 2
    return _run_master()


if __name__ == "__main__":
    raise SystemExit(main())
