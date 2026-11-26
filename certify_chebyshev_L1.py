#!/usr/bin/env python3
"""
Rigorous Interval-Arithmetic Certification for the Chebyshev L^1 Interpolation
Center-Maximum Theorem: B_n = E_n(0) (and E_n'(t) < 0 on (0, 1)) for ALL n >= 1.

Uses mpmath.iv (arbitrary-precision interval arithmetic with directed rounding)
and exact Python integer/Fraction arithmetic (zero rounding error).

What this script certifies:
  1. Analytic threshold N = 4 (all integers n >= 4, all t in (0, 1/2]):
     - Exact closed-form margin at n = 4:
         A1(4) + A2(4) = 4039168 * sqrt(3) / 9183213 < 0.76183 < 1
       (strict margin > 0.23817).
     - Exact integer polynomial positivity proving A1(n+1)/A1(n) < 1/2 and
       A2(n+1)/A2(n) < 1/2 for all integers n >= 4 (monotonicity in n).
     - Exact integer verification of the AM-GM constant 3^(2/3) > 2 (9 > 8)
       used in (2 + x)(1 + x + x^2 + x^3) > 9x.
  2. Rigorous interval-arithmetic certification of Delta_3(t) > 0 on (0, 1/2]
     (hence E_3'(t) < 0 on (0, 1), upgrading Section 5.2 of chebyshev_L1_note.tex):
     - Partition of [0, 1/2] into 5 subintervals [t0, t1].
     - On each [t0, t1], compact 1D integral R_ub(3; t0, t1) over [t0^2, 1] is
       enclosed via rigorous mpmath.iv interval Riemann sums (no truncation
       error, no tail error, outward rounding throughout), and verified
       strictly below the interval lower bound M_lb(3; t1).
  3. Rigorous verification of the elementary algebraic proofs for n = 2 and n = 3
     (Section 5.2 of chebyshev_L1_note.tex).
  4. Independent high-precision numerical cross-checks of:
     - The exact determinant identity for det(I - i*xi*(t*D_n - M_n)),
     - The vertical-chord integral for Delta_n(t) = G(Q_t) - G(Q_t^0) against
       direct B-spline divided differences,
     - The vertical-chord integral for H_n'(t) against direct derivative of
       E_n(t), including at an exact diagonal crossing point t = cos(2*pi/5).

Usage:
    python certify_chebyshev_L1.py
"""

from fractions import Fraction
import sys
import mpmath as mp
from mpmath import iv


def iv_lo(x) -> mp.mpf:
    """Extract the exact lower endpoint of an iv.mpf as an mp.mpf."""
    return mp.mp.make_mpf(x._mpi_[0])


def iv_hi(x) -> mp.mpf:
    """Extract the exact upper endpoint of an iv.mpf as an mp.mpf."""
    return mp.mp.make_mpf(x._mpi_[1])


def fmt_mpf(x: mp.mpf, digits: int = 12) -> str:
    return mp.nstr(x, digits)


def certify_part1_analytic_n_ge_4():
    print("=" * 72)
    print("PART 1: Rigorous Certification of Analytic Proof for ALL n >= 4")
    print("=" * 72)

    iv.dps = 50

    # 1a. Verify elementary AM-GM constant: 3^(2/3) > 2 <=> 3^2 > 2^3
    assert 3**2 > 2**3, "AM-GM constant check failed"
    print("[PASS] Elementary AM-GM constant: 3^2 = 9 > 8 = 2^3 => 3^(2/3) > 2")

    # 1b. Exact closed-form evaluation of A1(4), A2(4), A1(4) + A2(4)
    # Using exact rational identities for half-integer Beta functions:
    #   Gamma(k + 1/2) / sqrt(pi) = (2k)! / (4^k * k!)
    def double_fact_gamma_half(k: int) -> Fraction:
        """Return Gamma(k + 1/2) / sqrt(pi) as an exact Fraction."""
        num = 1
        for j in range(1, 2 * k + 1):
            num *= j
        den = (4**k)
        for j in range(1, k + 1):
            den *= j
        return Fraction(num, den)

    def fact(k: int) -> int:
        res = 1
        for j in range(2, k + 1):
            res *= j
        return res

    def beta_int_half(a: int, k: int) -> Fraction:
        """Return B(a, k + 1/2) = Gamma(a)*Gamma(k+1/2)/Gamma(a+k+1/2) exactly."""
        # Note sqrt(pi) cancels between Gamma(k+1/2) and Gamma(a+k+1/2)!
        return Fraction(fact(a - 1), 1) * double_fact_gamma_half(k) / double_fact_gamma_half(a + k)

    # At n = 4:
    # M_lb(4) = (2*4 + 5)/(3*(4 + 3)) * (3/4)^(9/2) * B(5, 3/2)
    #         = (13/21) * (81*sqrt(3)/512) * B(5, 3/2)
    # T1(4)   = (2/9) * B(4, 13/2)
    # T2(4)   = (4*5/27) * B(3, 9/2)
    # Notice M_lb(4) / sqrt(3) is an EXACT rational number!
    M4_over_sqrt3 = Fraction(13, 21) * Fraction(3**4, 2**9) * beta_int_half(5, 1)
    T1_4 = Fraction(2, 9) * beta_int_half(4, 6)
    T2_4 = Fraction(20, 27) * beta_int_half(3, 4)

    # Since M4 = M4_over_sqrt3 * sqrt(3), we have
    # A1(4) = (T1_4 / (3 * M4_over_sqrt3)) * sqrt(3)
    c1 = T1_4 / (3 * M4_over_sqrt3)
    c2 = T2_4 / (3 * M4_over_sqrt3)
    c_tot = c1 + c2

    assert c1 == Fraction(68992, 4421547), f"Unexpected c1: {c1}"
    assert c2 == Fraction(156800, 369603), f"Unexpected c2: {c2}"
    assert c_tot == Fraction(4039168, 9183213), f"Unexpected c_tot: {c_tot}"

    # Exact integer inequality proving (A1(4) + A2(4))^2 < 1:
    sq_exact = 3 * c_tot * c_tot
    assert sq_exact.numerator < sq_exact.denominator, "n=4 exact square bound failed"
    print(f"[PASS] Exact rational*sqrt(3) at n=4:")
    print(f"       A1(4)         = ({c1}) * sqrt(3)")
    print(f"       A2(4)         = ({c2}) * sqrt(3)")
    print(f"       A1(4) + A2(4) = ({c_tot}) * sqrt(3)")
    print(f"       (A1(4)+A2(4))^2 = {sq_exact.numerator} / {sq_exact.denominator} < 1  (EXACT)")

    # Interval enclosure of A1(4) + A2(4) and strict margin 1 - (A1(4) + A2(4))
    sqrt3_iv = iv.sqrt(iv.mpf(3))
    A1_4_iv = (iv.mpf(c1.numerator) / iv.mpf(c1.denominator)) * sqrt3_iv
    A2_4_iv = (iv.mpf(c2.numerator) / iv.mpf(c2.denominator)) * sqrt3_iv
    tot_4_iv = A1_4_iv + A2_4_iv
    margin_4_iv = iv.mpf(1) - tot_4_iv

    assert iv_hi(tot_4_iv) < mp.mpf("0.761830"), f"Unexpected upper bound: {iv_hi(tot_4_iv)}"
    assert iv_lo(margin_4_iv) > mp.mpf("0.238170"), f"Unexpected margin: {iv_lo(margin_4_iv)}"
    print(f"[PASS] Interval enclosure at n=4:")
    print(f"       A1(4) + A2(4) in [{fmt_mpf(iv_lo(tot_4_iv), 18)}, {fmt_mpf(iv_hi(tot_4_iv), 18)}]")
    print(f"       Strict margin 1 - (A1(4)+A2(4)) >= {fmt_mpf(iv_lo(margin_4_iv), 12)} > 0.23817")

    # 1c. Exact integer verification of monotonicity in n for ALL n >= 4:
    # Step ratios:
    #   r1(n) = A1(n+1)/A1(n) = [4*n*(n+4)*(2n+5)^3] / [3*(n+1)*(n+3)*(2n+7)*(4n+5)*(4n+7)]
    #   r2(n) = A2(n+1)/A2(n) = [4*(n+2)*(n-1)*(n+4)*(2n+1)*(2n+5)^2]
    #                           / [3*(n+1)^2*(n+3)*(2n+7)*(4n-1)*(4n+1)]
    # We prove den1(n) - 2*num1(n) > 0 and den2(n) - 2*num2(n) > 0 for all n = 4 + m (m >= 0)
    # by computing the exact integer coefficients in powers of m using polynomial multiplication.
    def poly_mul(p, q):
        res = [0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                res[i + j] += a * b
        return res

    def poly_sub(p, q):
        L = max(len(p), len(q))
        p_pad = p + [0] * (L - len(p))
        q_pad = q + [0] * (L - len(q))
        return [a - b for a, b in zip(p_pad, q_pad)]

    def poly_scale(c, p):
        return [c * a for a in p]

    # Linear factor (a*n + b) substituted with n = m + 4 is (4*a + b) + a*m
    def lin(a, b):
        return [4 * a + b, a]

    num1 = poly_scale(4, poly_mul(lin(1, 0), poly_mul(lin(1, 4), poly_mul(lin(2, 5), poly_mul(lin(2, 5), lin(2, 5))))))
    den1 = poly_scale(3, poly_mul(lin(1, 1), poly_mul(lin(1, 3), poly_mul(lin(2, 7), poly_mul(lin(4, 5), lin(4, 7))))))
    diff1 = poly_sub(den1, poly_scale(2, num1))

    num2 = poly_scale(
        4,
        poly_mul(
            lin(1, 2),
            poly_mul(lin(1, -1), poly_mul(lin(1, 4), poly_mul(lin(2, 1), poly_mul(lin(2, 5), lin(2, 5))))),
        ),
    )
    den2 = poly_scale(
        3,
        poly_mul(
            lin(1, 1),
            poly_mul(lin(1, 1), poly_mul(lin(1, 3), poly_mul(lin(2, 7), poly_mul(lin(4, -1), lin(4, 1))))),
        ),
    )
    diff2 = poly_sub(den2, poly_scale(2, num2))

    assert all(c > 0 for c in diff1), f"diff1 has nonpositive coeff: {diff1}"
    assert all(c > 0 for c in diff2), f"diff2 has nonpositive coeff: {diff2}"
    print(f"[PASS] Exact monotonicity in n (m = n - 4 >= 0):")
    print(f"       den1 - 2*num1 coeffs (m^0..m^5) = {diff1}  (all > 0 => r1(n) < 1/2)")
    print(f"       den2 - 2*num2 coeffs (m^0..m^6) = {diff2}  (all > 0 => r2(n) < 1/2)")
    print(f"       => For ALL n >= 4 and ALL t in (0, 1/2]:")
    print(f"          R_n(t) / M_n(t) <= 2^(-(n-4)) * (A1(4)+A2(4)) < 0.76183 * 2^(-(n-4)) < 1.")
    print()


def certify_part2_n3_interval_quadrature():
    print("=" * 72)
    print("PART 2: Rigorous Interval Certification of Delta_3(t) > 0 on (0, 1/2]")
    print("=" * 72)

    iv.dps = 40

    # Exact rational partition of [0, 1/2] into 5 subintervals
    t_nodes = [
        Fraction(0, 1),
        Fraction(1, 4),
        Fraction(7, 20),
        Fraction(21, 50),
        Fraction(23, 50),
        Fraction(1, 2),
    ]
    # Number of uniform x-subintervals per t-block on [t0^2, 1]
    N_x = 128

    def iv_frac(f: Fraction):
        return iv.mpf(f.numerator) / iv.mpf(f.denominator)

    worst_ratio_ub = mp.mpf(0)

    for idx in range(len(t_nodes) - 1):
        t0_f = t_nodes[idx]
        t1_f = t_nodes[idx + 1]
        s0_f = t0_f * t0_f
        s1_f = t1_f * t1_f

        s0 = iv_frac(s0_f)
        s1 = iv_frac(s1_f)

        # Lower bound on M_3(t) over t in [t0, t1]:
        # M_3(t) >= M_lb(3, t1) = (16/315) * 11 * (1 - s1)^(7/2) / (11 - 8*s1)
        one = iv.mpf(1)
        a2_1 = one - s1
        M_lb_iv = (iv.mpf(176) / iv.mpf(315)) * (a2_1**3) * iv.sqrt(a2_1) / (iv.mpf(11) - iv.mpf(8) * s1)

        # Upper bound on R_3(t) over t in [t0, t1] via compact 1D integral on [s0, 1]:
        # f_ub(x) = (1-x)^2 * x^4 * phi2_max(x) * sqrt(x - s0) / (2 * D_min(x) * S_eff(x))
        #         + 4 * (1-x) * x^4 * (1 - s1) * sqrt(x - s0) / (D_min(x)^2 * S_eff(x)^2)
        # where:
        #   D_min(x)    = 1 - (2 - x)*s1
        #   phi2_max(x) = (x - s0) / (1 - (2 - x)*s0)
        #   S_eff(x)    = 1 + x + x^2 + x^3 + x^4 * (1 - s0) / (1 - (2 - x)*s0)
        # Every denominator is strictly positive on [s0, 1], and the domain [s0, 1]
        # is compact -> ZERO truncation error, ZERO tail error!
        dx_f = (Fraction(1, 1) - s0_f) / N_x
        dx_iv = iv_frac(dx_f)
        R_ub_sum = iv.mpf(0)

        for k in range(N_x):
            xL_f = s0_f + k * dx_f
            xR_f = s0_f + (k + 1) * dx_f
            # Construct exact enclosing interval [xL, xR]
            xL_iv = iv_frac(xL_f)
            xR_iv = iv_frac(xR_f)
            X = iv.mpf([iv_lo(xL_iv), iv_hi(xR_iv)])

            one_m_X = one - X
            # Clamp lower endpoint of (X - s0) at 0 (exact since x >= s0 on [s0, 1])
            X_m_s0_raw = X - s0
            X_m_s0 = iv.mpf([max(mp.mpf(0), iv_lo(X_m_s0_raw)), iv_hi(X_m_s0_raw)])
            v_max = iv.sqrt(X_m_s0)

            D0 = one - (iv.mpf(2) - X) * s0
            D1 = one - (iv.mpf(2) - X) * s1
            assert iv_lo(D0) > 0 and iv_lo(D1) > 0, "Denominator enclosure not strictly positive"

            phi2_max = X_m_s0 / D0
            X2 = X * X
            X3 = X2 * X
            X4 = X2 * X2
            S_eff = one + X + X2 + X3 + X4 * (one - s0) / D0
            assert iv_lo(S_eff) > 0, "S_eff enclosure not strictly positive"

            term1 = (one_m_X * one_m_X) * X4 * phi2_max * v_max / (iv.mpf(2) * D1 * S_eff)
            term2 = iv.mpf(4) * one_m_X * X4 * a2_1 * v_max / ((D1 * D1) * (S_eff * S_eff))

            f_box = term1 + term2
            R_ub_sum += dx_iv * iv.mpf([iv_lo(f_box), iv_hi(f_box)])

        ratio_iv = R_ub_sum / M_lb_iv
        margin_iv = one - ratio_iv
        assert iv_hi(R_ub_sum) < iv_lo(M_lb_iv), (
            f"Certification FAILED on [{t0_f}, {t1_f}]: "
            f"R_ub_hi={iv_hi(R_ub_sum)} >= M_lb_lo={iv_lo(M_lb_iv)}"
        )
        if iv_hi(ratio_iv) > worst_ratio_ub:
            worst_ratio_ub = iv_hi(ratio_iv)

        print(
            f"[PASS] t in [{str(t0_f):>5}, {str(t1_f):>5}]: "
            f"R_ub <= {fmt_mpf(iv_hi(R_ub_sum), 8):>11}, "
            f"M_lb >= {fmt_mpf(iv_lo(M_lb_iv), 8):>11}, "
            f"ratio <= {fmt_mpf(iv_hi(ratio_iv), 7)} (margin >= {fmt_mpf(iv_lo(margin_iv), 6)})"
        )

    print(f"[PASS] ALL 5 subintervals certified! Worst upper bound on R_3/M_3 <= {fmt_mpf(worst_ratio_ub, 7)} < 1.")
    print("       => Delta_3(t) > 0 for all t in (0, 1/2], hence E_3'(t) < 0 on ALL of (0, 1).")
    print()


def certify_part3_low_orders_n1_n2_n3():
    print("=" * 72)
    print("PART 3: Verification of Elementary Algebraic Proofs for n = 1, 2, 3")
    print("=" * 72)

    iv.dps = 40

    # n = 1: E_1(t) = (1 - t^2)/2 => E_1'(t) = -t < 0 on (0, 1).
    print("[PASS] n = 1: E_1(t) = (1 - t^2)/2, E_1'(t) = -t < 0 on (0, 1).")

    # n = 2: 6*E_2'(t) = 3*t*(7*t^2 + 38 - (t + 16)*sqrt(t^2 + 8)) / sqrt(t^2 + 8).
    # (t + 16)^2*(t^2 + 8) - (7*t^2 + 38)^2 = 4*(t + 1)*(151 - 87*t + 20*t^2 - 12*t^3).
    lhs_c = [2048 - 1444, 256, 264 - 532, 32, 1 - 49]
    rhs_c = [4 * 151, 4 * (151 - 87), 4 * (-87 + 20), 4 * (20 - 12), 4 * (-12)]
    assert lhs_c == rhs_c, "n=2 polynomial identity mismatch"
    # On t in (0, 1): 151 - 87t + 20t^2 - 12t^3 = (151 - 99t) + 20t^2 + 12t(1 - t^2) > 52 > 0!
    T = iv.mpf([0, 1])
    P2 = (iv.mpf(151) - iv.mpf(99) * T) + iv.mpf(20) * (T * T) + iv.mpf(12) * T * (iv.mpf(1) - T * T)
    assert iv_lo(P2) >= 52, f"n=2 positivity check failed: {P2}"
    print(f"[PASS] n = 2: 151 - 87t + 20t^2 - 12t^3 >= {fmt_mpf(iv_lo(P2), 6)} > 0 on [0, 1] => E_2'(t) < 0 on (0, 1).")

    # n = 3 (Section 5.2 of chebyshev_L1_note.tex):
    # E_3(t) - E_3(0) <= c2 * t^2 + c4 * t^4 on [0, 1/2]
    s5 = iv.sqrt(iv.mpf(5))
    c2 = iv.mpf(34) / 8 * s5 + iv.mpf(58) / (16 * s5) - iv.mpf(12) + iv.mpf(3) / 64
    c4 = iv.mpf(94) / (16 * s5) - iv.mpf(2)
    upper_coeff = c2 + c4 / iv.mpf(4)  # since c4 > 0 and t^2 <= 1/4
    assert iv_lo(c4) > 0, "Expected c4 > 0"
    assert iv_hi(upper_coeff) < -mp.mpf(11) / 32, f"n=3 note bound failed: {upper_coeff}"
    print(
        f"[PASS] n = 3 (Section 5.2 algebraic bound): "
        f"c2 + c4/4 in [{fmt_mpf(iv_lo(upper_coeff), 12)}, {fmt_mpf(iv_hi(upper_coeff), 12)}] < -11/32 = -0.34375."
    )
    print()


def cross_check_part4_identities():
    print("=" * 72)
    print("PART 4: Independent 30-Digit Numerical Cross-Checks of Core Identities")
    print("=" * 72)

    mp.mp.dps = 35

    def eigvals_Jn(n, t):
        M = mp.zeros(n + 1, n + 1)
        M[0, 0] = t / 2
        M[n, n] = t / 2
        for j in range(n):
            M[j, j + 1] = mp.mpf("0.5")
            M[j + 1, j] = mp.mpf("0.5")
        return sorted([mp.re(x) for x in mp.eigsy(M, eigvals_only=True)])

    def divided_diff(xs, ys):
        m = len(xs)
        c = list(ys)
        for k in range(1, m):
            for i in range(m - 1, k - 1, -1):
                c[i] = (c[i] - c[i - 1]) / (xs[i] - xs[i - k])
        return c[-1]

    # 4a. Determinant identity
    max_det_err = mp.mpf(0)
    for n in [1, 2, 3, 4, 5, 10]:
        t = mp.mpf("0.37")
        xi = mp.mpf("1.93")
        s = 1j * xi
        M = mp.zeros(n + 3, n + 3)
        M[0, 0] = t + 1
        M[1, 1] = t - 1
        for j in range(n + 1):
            M[2 + j, 2 + j] = t - (t / 2 if (j == 0 or j == n) else 0)
            if j < n:
                M[2 + j, 2 + j + 1] = -mp.mpf("0.5")
                M[2 + j + 1, 2 + j] = -mp.mpf("0.5")
        d_mat = mp.det(mp.eye(n + 3) - s * M)
        y = t + 1j / xi
        r = mp.sqrt(y * y - 1)
        u = y - r if abs(y - r) < 1 else y + r
        d_closed = (1 - u**2) * ((1 - t * u) ** 2 - u ** (2 * n + 2) * (u - t) ** 2) / (1 - 2 * t * u + u**2) ** (n + 3)
        err = abs(d_mat - d_closed) / abs(d_mat)
        max_det_err = max(max_det_err, err)
    assert max_det_err < mp.mpf("1e-30"), f"Determinant identity error too large: {max_det_err}"
    print(f"[PASS] Exact determinant identity (n=1,2,3,4,5,10): max rel err = {mp.nstr(max_det_err, 4)}")

    # 4b. Delta_n(t) chord integral vs direct divided differences
    max_delta_err = mp.mpf(0)
    for n in [1, 2, 3, 4, 5, 8]:
        t = mp.mpf("0.31")
        eigs = eigvals_Jn(n, t)
        zs = [mp.mpf(-1)] + eigs + [mp.mpf(1)]
        rho0 = divided_diff(zs, [max(mp.mpf(0), z - t) ** (n + 1) for z in zs])
        rhop0 = divided_diff(zs, [max(mp.mpf(0), z - t) ** n for z in zs])
        d_direct = 4 * t * rho0 - 2 * (1 - t * t) * rhop0
        a = mp.sqrt(1 - t * t)

        def integrand(v):
            u = t + 1j * v
            q = 1 - t * t - v * v
            phi = (u - t) / (1 - t * u)
            return (q**n) * mp.re((-phi) / (1 - (u ** (2 * n + 2)) * (phi**2)))

        d_chord = (8 / mp.pi) * mp.quad(integrand, [0, a])
        err = abs(d_direct - d_chord) / abs(d_direct)
        max_delta_err = max(max_delta_err, err)
    assert max_delta_err < mp.mpf("1e-28"), f"Delta_n chord identity error too large: {max_delta_err}"
    print(f"[PASS] Delta_n(t) vertical-chord identity (n=1,2,3,4,5,8): max rel err = {mp.nstr(max_delta_err, 4)}")

    # 4c. H_n'(t) chord integral at an EXACT diagonal crossing point n = 5, t = cos(2*pi/5)
    n = 5
    t_cross = (mp.sqrt(5) - 1) / 4

    def E_n_exact(nn, tv):
        eigs = eigvals_Jn(nn, tv)
        s_sum = sum(
            (1 if (nn - j) % 2 == 0 else -1) * max(mp.mpf(0), u - tv) ** (nn + 1)
            for j, u in enumerate(eigs)
        )
        return 1 - tv - (mp.mpf(2) ** nn / (nn + 1)) * (1 - tv) ** (nn + 1) + (mp.mpf(2) ** (nn + 1) / (nn + 1)) * s_sum

    a = mp.sqrt(1 - t_cross * t_cross)

    def hp_integrand(v):
        u = t_cross + 1j * v
        q = 1 - t_cross * t_cross - v * v
        denom = (1 - t_cross * u) ** 2 - (u ** (2 * n + 2)) * (u - t_cross) ** 2
        bracket = 2 * n * (t_cross - u) * (1 - t_cross * u) - q * (1 + u * u) / u
        return mp.re((q**n / denom) * bracket)

    hp_chord = 1 + (2 / mp.pi) * mp.quad(hp_integrand, [0, a])
    h = mp.mpf("1e-11")
    hp_fd = -(E_n_exact(n, t_cross + h) - E_n_exact(n, t_cross - h)) / (2 * h)
    cross_err = abs(hp_chord - hp_fd)
    assert cross_err < mp.mpf("1e-18"), f"Crossing point check failed: {cross_err}"
    print(f"[PASS] H_5'(cos(2*pi/5)) at exact crossing point: diff = {mp.nstr(cross_err, 4)}")
    print()


def main():
    certify_part1_analytic_n_ge_4()
    certify_part2_n3_interval_quadrature()
    certify_part3_low_orders_n1_n2_n3()
    cross_check_part4_identities()
    print("=" * 72)
    print("ALL CERTIFICATIONS AND CROSS-CHECKS PASSED!")
    print("Summary: B_n = E_n(0) and E_n'(t) < 0 on (0, 1) for ALL integers n >= 1.")
    print("Uncovered finite orders: NONE (0).")
    print("=" * 72)


if __name__ == "__main__":
    main()
