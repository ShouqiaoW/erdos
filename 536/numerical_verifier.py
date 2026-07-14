#!/usr/bin/env python3
"""
Finite-arithmetic verifier for the Erdős 536 proof.

The paper contains every mathematical implication needed for the theorem.
This companion program independently checks the finite arithmetic and
finite combinatorics printed there:

  * squarefree product-law and unit-deletion normalizations;
  * the cap-set constant substitution;
  * the explicit prime-band, survival, buffer, and anchor constants;
  * five-state and conditional missing-petal probabilities;
  * finite atom-by-atom instances of factorial insertion;
  * all nine-mark rank counts and inverse-matrix projection constants;
  * elementary balance identities and candidate-band separation.

It uses exact Fraction arithmetic and rigorous rational intervals.  It uses
no binary floating point, random sampling, network access, or external
packages.

This program does not prove the cited prime estimates, Brun--Titchmarsh, or
the Ellenberg--Gijswijt theorem.  It also does not replace the paper's
Stieltjes, total-variation, Poisson, pivot-summation, or limit arguments.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial
from typing import Callable, Iterable, Sequence


PASS_COUNT = 0
SANITY_COUNT = 0


def check(identifier: str, condition: bool, message: str) -> None:
    """Record one paper-facing exact assertion."""
    global PASS_COUNT
    if not condition:
        raise AssertionError(f"FAILED [{identifier}]: {message}")
    PASS_COUNT += 1
    print(f"PASS [{identifier}]: {message}")


def sanity(identifier: str, condition: bool, message: str) -> None:
    """Record one optional finite regression assertion."""
    global SANITY_COUNT
    if not condition:
        raise AssertionError(f"FAILED [{identifier}]: {message}")
    SANITY_COUNT += 1
    print(f"PASS [{identifier}]: {message}")


def subsets(items: Sequence[int]) -> Iterable[tuple[int, ...]]:
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def product_int(values: Iterable[int]) -> int:
    answer = 1
    for value in values:
        answer *= value
    return answer


def product_q(values: Iterable[Fraction]) -> Fraction:
    answer = Fraction(1)
    for value in values:
        answer *= value
    return answer


def poisson_product_mass(
    subset: frozenset[int], probabilities: Sequence[Fraction]
) -> Fraction:
    return product_q(
        probabilities[i] if i in subset else 1 - probabilities[i]
        for i in range(len(probabilities))
    )


def log_atanh_interval(x: Fraction, terms: int = 24) -> tuple[Fraction, Fraction]:
    """
    Rigorous interval for log(x), for x >= 1.

    log(x) = 2 sum_{n>=0} z^(2n+1)/(2n+1), z=(x-1)/(x+1).
    The omitted positive tail is bounded by replacing every denominator by
    2*terms+1 and summing a geometric series.
    """
    if x < 1:
        raise ValueError("log_atanh_interval requires x >= 1")
    if x == 1:
        return Fraction(0), Fraction(0)
    z = (x - 1) / (x + 1)
    z2 = z * z
    term = z
    partial = Fraction(0)
    for n in range(terms):
        partial += term / (2 * n + 1)
        term *= z2
    lower = 2 * partial
    tail = 2 * term / (2 * terms + 1) / (1 - z2)
    return lower, lower + tail


def exp_positive_partial(x: Fraction, degree: int) -> Fraction:
    """Positive Taylor partial sum for exp(x)."""
    return sum((x**n) / factorial(n) for n in range(degree + 1))


def section_header(number: int, title: str) -> None:
    print(f"\n[{number}] {title}")


# ---------------------------------------------------------------------------
# Paper-facing checks
# ---------------------------------------------------------------------------


def verify_structural() -> None:
    section_header(1, "Structural product laws")
    primes = (2, 3, 5, 7)
    all_subsets = list(subsets(primes))
    z_value = product_q(Fraction(p + 1, p) for p in primes)
    reciprocal_sum = sum(
        Fraction(1, product_int(subset)) for subset in all_subsets
    )
    check(
        "STR-01",
        reciprocal_sum == z_value,
        "sum_S 1/d(S) equals product_p (1+1/p)",
    )

    masses: dict[frozenset[int], Fraction] = {}
    for subset in all_subsets:
        support = frozenset(subset)
        masses[support] = Fraction(1, 1) / (
            z_value * product_int(subset)
        )
    check(
        "STR-02",
        sum(masses.values()) == 1,
        "mu_R is exactly normalized on a four-prime test set",
    )
    for p in primes:
        marginal = sum(mass for support, mass in masses.items() if p in support)
        check(
            f"STR-02-p{p}",
            marginal == Fraction(1, p + 1),
            f"the p={p} marginal is exactly 1/(p+1)",
        )

    for p in primes:
        zero_mass = (1 - Fraction(1, p)) * (1 + Fraction(1, p))
        positive_mass = Fraction(1, p * p)
        check(
            f"STR-03-p{p}",
            zero_mass == 1 - Fraction(1, p * p),
            f"valuation zero has mass 1-p^(-2) for p={p}",
        )
        check(
            f"STR-04-p{p}",
            zero_mass + positive_mass == 1,
            f"valuation zero and valuations >=2 normalize for p={p}",
        )


def verify_capset() -> None:
    section_header(2, "Cap-set substitution")
    check(
        "CAP-01",
        Fraction(7, 4) == 3 * Fraction(7, 12),
        "the t=1/2 scalar is 3*(7/12)",
    )
    kappa_cube = 4 * Fraction(7, 12) ** 3
    check(
        "CAP-02",
        kappa_cube == Fraction(343, 432) and kappa_cube < 1,
        "kappa_cap^3=343/432<1",
    )


def verify_parameters() -> None:
    section_header(3, "Explicit prime-band parameters")
    a = Fraction(23, 25)
    a0 = Fraction(24, 25)
    theta = Fraction(1, 200)
    alpha = Fraction(8, 25)
    q = Fraction(24, 25)
    gamma = Fraction(1, 50)
    delta = Fraction(1, 100)
    buffer = 350
    r0 = 75
    m = 374

    log3_lo, log3_hi = log_atanh_interval(Fraction(3))
    printed_lower = (
        Fraction(1)
        + Fraction(1, 12)
        + Fraction(1, 80)
        + Fraction(1, 448)
        + Fraction(1, 2304)
    )
    check(
        "PAR-01",
        0 < a < a0 < 1 and 0 < theta < 1 and alpha == a0 / 3,
        "0<a<a0<1, 0<theta<1, and alpha=a0/3",
    )
    check(
        "PAR-02",
        printed_lower > Fraction(549, 500) and log3_lo > printed_lower,
        "the positive atanh series certifies log(3)>549/500",
    )
    endpoint_lower = a * (1 - theta) * Fraction(549, 500)
    check(
        "PAR-03",
        endpoint_lower == Fraction(2512773, 2500000)
        and endpoint_lower > 1,
        "a(1-theta)log(3)>2512773/2500000>1",
    )
    check(
        "PAR-04",
        a * log3_lo > 1 and Fraction(1, a) < log3_lo,
        "a log(3)>1 and the pivot geometric ratio is <1",
    )
    check(
        "PAR-05",
        3 * alpha == a0 and (a0 - a) * r0 == 3,
        "the floor loss is absorbed for every real s>=R0=75",
    )
    check(
        "PAR-06",
        alpha * r0 == 24 and m == 24 + buffer,
        "floor(alpha R0)=24 and m=374",
    )

    drift_upper = (q - 1) * gamma + gamma * gamma / 2
    check(
        "PAR-07",
        drift_upper == Fraction(-3, 5000) < 0,
        "the explicit exponential-supermartingale drift is negative",
    )

    exp_3p5 = exp_positive_partial(Fraction(7, 2), 7)
    check(
        "PAR-08",
        exp_3p5 == Fraction(66007, 2048) and exp_3p5 > 32,
        "the degree-7 Taylor lower bound gives exp(7/2)>32",
    )
    buffer_bound = Fraction(374 * factorial(4), 74**4)
    check(
        "PAR-09",
        buffer_bound == Fraction(561, 1874161)
        and buffer_bound < delta / 2,
        "374 exp(-74)<561/1874161<delta/2",
    )
    tail_bound = Fraction(800 * factorial(3), 75**3)
    check(
        "PAR-10",
        tail_bound == Fraction(64, 5625) and tail_bound < Fraction(1, 8),
        "800 exp(-75)<64/5625<1/8",
    )
    check(
        "PAR-11",
        1 - Fraction(1, 8) - Fraction(1, 8) == Fraction(3, 4),
        "the two union bounds retain conditional probability 3/4",
    )
    check(
        "PAR-12",
        log3_lo < log3_hi,
        "the rigorous rational interval for log(3) has positive width",
    )

    q_intervals = (
        (Fraction(r0 - 1), Fraction(r0) - Fraction(7, 8)),
        (Fraction(r0) - Fraction(3, 4), Fraction(r0) - Fraction(5, 8)),
        (Fraction(r0) - Fraction(1, 2), Fraction(r0) - Fraction(3, 8)),
        (Fraction(r0) - Fraction(1, 4), Fraction(r0) - Fraction(1, 8)),
    )
    positive = all(left < right for left, right in q_intervals)
    inside = all(Fraction(r0 - 1) <= left < right < r0 for left, right in q_intervals)
    disjoint = all(
        q_intervals[i][1] < q_intervals[i + 1][0]
        for i in range(len(q_intervals) - 1)
    )
    check(
        "PAR-13",
        positive and inside and disjoint,
        "the four explicit buffer intervals are positive and disjoint",
    )


def verify_categories() -> None:
    section_header(4, "Five-state and conditional laws")
    for p in (2, 3, 5, 11, 101):
        r = Fraction(1, p + 1)
        h = r / 3
        empty = 1 - 4 * h
        check(
            f"CAT-01-p{p}",
            empty + 4 * h == 1 and empty >= 0,
            f"the five probabilities normalize and are nonnegative for p={p}",
        )
        check(
            f"CAT-02-p{p}",
            3 * h == r,
            f"each of the three state supports has marginal r_p for p={p}",
        )
        check(
            f"CAT-03-p{p}",
            r / (1 - r) == Fraction(1, p),
            f"the root inclusion odds are 1/p for p={p}",
        )
        check(
            f"CAT-04-p{p}",
            h / r == Fraction(1, 3),
            f"root colours are conditionally uniform for p={p}",
        )
        missing = h / (1 - r)
        check(
            f"CAT-05-p{p}",
            missing == Fraction(1, 3 * p),
            f"the conditional missing-petal probability is 1/(3p) for p={p}",
        )
        odds = missing / (1 - missing)
        check(
            f"CAT-06-p{p}",
            odds == Fraction(1, 3 * p - 1) <= Fraction(1, p),
            f"missing-petal insertion odds are 1/(3p-1)<=1/p for p={p}",
        )


def verify_anchors() -> None:
    section_header(5, "Poisson constants and anchor geometry")
    check(
        "POI-01",
        8 + 16 + 8 == 32 and Fraction(32, 2) == 16,
        "the local total-variation constant is 16",
    )
    k_left, k_right = Fraction(9, 20), Fraction(11, 20)
    a_left, a_right = Fraction(12, 25), Fraction(13, 25)
    delta = Fraction(1, 100)
    check(
        "ANC-01",
        k_left < a_left < a_right < k_right,
        "the z-anchor interval lies strictly inside the macro interval",
    )
    t_lo = a_left - delta
    t_hi = a_right + delta
    check(
        "ANC-02",
        t_lo == Fraction(47, 100) and t_hi == Fraction(53, 100),
        "adaptive anchor centres lie in [47/100,53/100]",
    )
    w_test = Fraction(1, 10)
    check(
        "ANC-03",
        t_lo - w_test / 8 > k_left and t_hi + w_test / 8 < k_right,
        "for w<=1/10 both correcting intervals lie in the macro interval",
    )
    check(
        "ANC-04",
        (w_test / 8) - (-w_test / 8) == w_test / 4,
        "each correcting interval has length w/4",
    )
    z_lo, z_hi = a_left, a_right + delta
    x_lo, x_hi = z_lo - w_test / 8, z_hi + w_test / 8
    check(
        "ANC-05",
        k_left < x_lo <= x_hi < k_right,
        "the corrected totals remain in J for sufficiently small w",
    )
    check(
        "ANC-06",
        2 * (w_test / 8) == w_test / 4 < w_test,
        "two w/8 errors give total range at most w/4<w",
    )


def verify_insertion() -> None:
    section_header(6, "Factorial insertion")
    probabilities = (
        Fraction(1, 3),
        Fraction(2, 5),
        Fraction(1, 7),
        Fraction(3, 8),
    )
    ground = tuple(range(len(probabilities)))

    for d in (1, 2, 3):
        atomwise_ok = True
        tuple_count_left = 0
        tuple_count_right = 0
        for subset_tuple in subsets(ground):
            support = frozenset(subset_tuple)
            for deleted in permutations(sorted(support), d):
                tuple_count_left += 1
                residual = support.difference(deleted)
                lhs = poisson_product_mass(support, probabilities)
                rhs = poisson_product_mass(residual, probabilities) * product_q(
                    probabilities[p] / (1 - probabilities[p])
                    for p in deleted
                )
                atomwise_ok = atomwise_ok and lhs == rhs
        for residual_tuple in subsets(ground):
            residual = frozenset(residual_tuple)
            for deleted in permutations(
                sorted(set(ground).difference(residual)), d
            ):
                tuple_count_right += 1
        check(
            f"FI-01-d{d}",
            atomwise_ok,
            f"the insertion coefficient identity holds atom by atom for d={d}",
        )
        check(
            f"FI-02-d{d}",
            tuple_count_left == tuple_count_right,
            f"deletion and insertion tuples are in bijection for d={d}",
        )

    def test_function(
        support: frozenset[int], deleted: tuple[int, ...]
    ) -> Fraction:
        return Fraction(
            (1 + sum(support)) * (1 + sum((j + 1) * p for j, p in enumerate(deleted))),
            1,
        )

    for d in (1, 2):
        lhs = Fraction(0)
        for subset_tuple in subsets(ground):
            support = frozenset(subset_tuple)
            mass = poisson_product_mass(support, probabilities)
            lhs += mass * sum(
                test_function(support, deleted)
                for deleted in permutations(sorted(support), d)
            )
        rhs = Fraction(0)
        for residual_tuple in subsets(ground):
            residual = frozenset(residual_tuple)
            mass = poisson_product_mass(residual, probabilities)
            for deleted in permutations(
                sorted(set(ground).difference(residual)), d
            ):
                full = residual.union(deleted)
                odds = product_q(
                    probabilities[p] / (1 - probabilities[p])
                    for p in deleted
                )
                rhs += mass * odds * test_function(full, deleted)
        check(
            f"FI-03-d{d}",
            lhs == rhs,
            f"the full factorial insertion sum agrees exactly for d={d}",
        )


MARKS = tuple(product((-1, 0, 1), repeat=2))


def det(v: tuple[int, int], w: tuple[int, int]) -> int:
    return v[0] * w[1] - v[1] * w[0]


def first_rank_two_indices(
    sequence: Sequence[tuple[int, int]]
) -> tuple[int, int] | None:
    first = next((i for i, mark in enumerate(sequence) if mark != (0, 0)), None)
    if first is None:
        return None
    second = next(
        (j for j in range(first + 1, len(sequence)) if det(sequence[first], sequence[j]) != 0),
        None,
    )
    if second is None:
        return (first + 1, 0)
    return (first + 1, second + 1)


def verify_pivots() -> None:
    section_header(7, "Pivot marks and local linear algebra")
    nonzero = tuple(mark for mark in MARKS if mark != (0, 0))
    check("PIV-01", len(MARKS) == 9 and len(nonzero) == 8, "there are 9 marks and 8 nonzero marks")

    line_counts = {v: sum(det(v, w) == 0 for w in MARKS) for v in nonzero}
    check(
        "PIV-02",
        set(line_counts.values()) == {3},
        "every nonzero mark line contains exactly 3 grid marks",
    )
    independent_pairs = tuple(
        (v, w) for v in nonzero for w in MARKS if det(v, w) != 0
    )
    check(
        "PIV-03",
        len(independent_pairs) == 48,
        "there are exactly 48 ordered noncollinear direction pairs",
    )
    determinants = {abs(det(v, w)) for v, w in independent_pairs}
    check(
        "PIV-04",
        determinants == {1, 2},
        "all nonzero mark determinants have absolute value 1 or 2",
    )
    row_norms: list[Fraction] = []
    for v, w in independent_pairs:
        determinant = abs(det(v, w))
        # Inverse of matrix [v w]: rows (w_y,-w_x) and (-v_y,v_x).
        row_norms.append(Fraction(abs(w[1]) + abs(w[0]), determinant))
        row_norms.append(Fraction(abs(v[1]) + abs(v[0]), determinant))
    check(
        "PIV-05",
        max(row_norms) == 2,
        "the maximum inverse row l1 norm is exactly 2",
    )

    mass_ok = True
    rank_one_ok = True
    for k in range(1, 9):
        for i in range(1, k + 1):
            rank_one_lhs = Fraction(8 * 3 ** (k - i), 9**k)
            rank_one_rhs = Fraction(8, 3 ** (k + i))
            rank_one_ok = rank_one_ok and rank_one_lhs == rank_one_rhs
            for j in range(i + 1, k + 1):
                lhs = Fraction(
                    8 * 3 ** (j - i - 1) * 6 * 9 ** (k - j),
                    9**k,
                )
                rhs = Fraction(16, 3 ** (i + j))
                mass_ok = mass_ok and lhs == rhs
    check(
        "PIV-06",
        mass_ok,
        "the rank-two cylinder mass is 16*3^(-i-j)",
    )
    check(
        "PIV-07",
        rank_one_ok,
        "the rank-one cylinder mass is 8*3^(-K-i)",
    )

    enumeration_ok = True
    for k in range(1, 6):
        rank_zero = 0
        rank_one: defaultdict[int, int] = defaultdict(int)
        rank_two: defaultdict[tuple[int, int], int] = defaultdict(int)
        for sequence in product(MARKS, repeat=k):
            ranks = first_rank_two_indices(sequence)
            if ranks is None:
                rank_zero += 1
            elif ranks[1] == 0:
                rank_one[ranks[0]] += 1
            else:
                rank_two[ranks] += 1
        enumeration_ok = enumeration_ok and rank_zero == 1
        for i in range(1, k + 1):
            enumeration_ok = enumeration_ok and (
                rank_one[i] == 8 * 3 ** (k - i)
            )
            for j in range(i + 1, k + 1):
                expected = 8 * 3 ** (j - i - 1) * 6 * 9 ** (k - j)
                enumeration_ok = enumeration_ok and rank_two[(i, j)] == expected
        enumeration_ok = enumeration_ok and (
            rank_zero + sum(rank_one.values()) + sum(rank_two.values()) == 9**k
        )
    check(
        "PIV-08",
        enumeration_ok,
        "exhaustive mark strings through K=5 agree with every rank formula",
    )

    a = Fraction(23, 25)
    theta = Fraction(1, 200)
    log3_lo, _ = log_atanh_interval(Fraction(3))
    check(
        "PIV-09",
        Fraction(1, a) < log3_lo,
        "the ordered-rank geometric series has ratio below one",
    )
    check(
        "PIV-10",
        a * (1 - theta) * log3_lo - 1 > 0,
        "the endpoint exponent a(1-theta)log(3)-1 is positive",
    )


def verify_bands() -> None:
    section_header(8, "Balance and candidate-band arithmetic")
    states = (
        (0, 1, 1),  # Y+Z
        (1, 0, 1),  # X+Z
        (1, 1, 0),  # X+Y
    )
    differences = {
        tuple(states[i][k] - states[j][k] for k in range(3))
        for i in range(3)
        for j in range(i + 1, 3)
    }
    expected = {(-1, 1, 0), (-1, 0, 1), (0, -1, 1)}
    check(
        "FLAT-01",
        differences == expected,
        "state-log differences are exactly pairwise differences of X,Y,Z",
    )

    theta = Fraction(1, 200)
    b0 = Fraction(1, 2)
    exponents = [b0 * theta ** (2 * j) for j in range(12)]
    check(
        "FLAT-02",
        all(value > 0 for value in exponents),
        "all fixed candidate-band exponents are positive",
    )
    check(
        "FLAT-03",
        all(exponents[j + 1] < theta * exponents[j] for j in range(11)),
        "b_(j+1)=theta^2 b_j<theta b_j, so adjacent bands separate",
    )

    test_values = (Fraction(3, 2), Fraction(4, 5), Fraction(7, 6))
    lhs = product_q(test_values) - 1
    rhs = sum(
        (test_values[i] - 1) * product_q(test_values[:i])
        for i in range(len(test_values))
    )
    check(
        "FLAT-04",
        lhs == rhs,
        "the product-density telescoping identity is exact",
    )


PAPER_SECTIONS: dict[str, Callable[[], None]] = {
    "structural": verify_structural,
    "capset": verify_capset,
    "parameters": verify_parameters,
    "categories": verify_categories,
    "anchors": verify_anchors,
    "insertion": verify_insertion,
    "pivots": verify_pivots,
    "bands": verify_bands,
}


# ---------------------------------------------------------------------------
# Optional small exhaustive regressions
# ---------------------------------------------------------------------------


def sanity_pair_product_valuations() -> None:
    ok = True
    for a_val, b_val, c_val in product(range(7), repeat=3):
        maxima = (
            max(a_val, b_val),
            max(a_val, c_val),
            max(b_val, c_val),
        )
        if maxima[0] != maxima[1] or maxima[0] != maxima[2]:
            continue
        top = maxima[0]
        petals = (top - c_val, top - b_val, top - a_val)
        ok = ok and all(value >= 0 for value in petals)
        ok = ok and sum(value > 0 for value in petals) <= 1
        t_val = a_val + b_val + c_val - 2 * top
        ok = ok and t_val >= 0
        ok = ok and t_val + petals[0] + petals[1] == a_val
        ok = ok and t_val + petals[0] + petals[2] == b_val
        ok = ok and t_val + petals[1] + petals[2] == c_val
    sanity(
        "SAN-01",
        ok,
        "all valuation triples through exponent 6 obey the pair-product formulas",
    )


def sanity_squarefree_unions() -> None:
    primes = (2, 3, 5, 7)
    supports = tuple(frozenset(s) for s in subsets(primes))
    products = {support: product_int(support) for support in supports}

    def integer_lcm(a: int, b: int) -> int:
        # Products are squarefree over the same prime ground set.
        sa = next(s for s, value in products.items() if value == a)
        sb = next(s for s, value in products.items() if value == b)
        return product_int(sa | sb)

    ok = True
    for triple in combinations(supports, 3):
        s1, s2, s3 = triple
        union_equal = (s1 | s2) == (s1 | s3) == (s2 | s3)
        p1, p2, p3 = (products[s] for s in triple)
        lcm_equal = (
            integer_lcm(p1, p2)
            == integer_lcm(p1, p3)
            == integer_lcm(p2, p3)
        )
        ok = ok and union_equal == lcm_equal
    sanity(
        "SAN-02",
        ok,
        "equal squarefree pairwise lcms are exactly equal pairwise unions",
    )


def is_admissible_family(family: Sequence[frozenset[int]]) -> bool:
    for s1, s2, s3 in combinations(family, 3):
        if (s1 | s2) == (s1 | s3) == (s2 | s3):
            return False
    return True


def sanity_small_capacity() -> None:
    primes = (2, 3, 5)
    supports = tuple(frozenset(s) for s in subsets(primes))
    d_value = {support: product_int(support) for support in supports}
    thresholds = sorted(set(d_value.values()))
    capacity_values: dict[int, int] = {}
    for threshold in thresholds:
        available = tuple(s for s in supports if d_value[s] <= threshold)
        best = 0
        for mask in range(1 << len(available)):
            family = tuple(
                available[i] for i in range(len(available)) if mask & (1 << i)
            )
            if len(family) > best and is_admissible_family(family):
                best = len(family)
        capacity_values[threshold] = best
    integral = Fraction(0)
    for left, right in zip(thresholds, thresholds[1:]):
        integral += capacity_values[left] * (
            Fraction(1, left) - Fraction(1, right)
        )
    integral += Fraction(capacity_values[thresholds[-1]], thresholds[-1])
    z_value = product_q(Fraction(p + 1, p) for p in primes)
    sanity(
        "SAN-03",
        0 <= integral <= z_value,
        "the exact three-prime moving-prefix capacity lies in [0,Z_R]",
    )


def cube_word_support(word: tuple[int, ...]) -> frozenset[int]:
    support = {0}  # common support
    for i, state in enumerate(word):
        x, y, z = 3 * i + 1, 3 * i + 2, 3 * i + 3
        contributions = ({y, z}, {x, z}, {x, y})
        support.update(contributions[state])
    return frozenset(support)


def sanity_pair_product_cubes() -> None:
    ok = True
    for dimension in (1, 2, 3):
        words = tuple(product(range(3), repeat=dimension))
        supports = {word: cube_word_support(word) for word in words}
        ok = ok and len(set(supports.values())) == 3**dimension
        for base in words:
            for direction in words:
                if all(value == 0 for value in direction):
                    continue
                line = tuple(
                    tuple((base[i] + scalar * direction[i]) % 3 for i in range(dimension))
                    for scalar in range(3)
                )
                s0, s1, s2 = (supports[word] for word in line)
                ok = ok and (s0 | s1) == (s0 | s2) == (s1 | s2)
    sanity(
        "SAN-04",
        ok,
        "canonical pair-product cubes through H=3 map every affine line to equal unions",
    )


def run_self_tests() -> None:
    print("\n[optional] Exhaustive finite regressions")
    sanity_pair_product_valuations()
    sanity_squarefree_unions()
    sanity_small_capacity()
    sanity_pair_product_cubes()
    print("\nOptional self-tests completed successfully.")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Exact finite-arithmetic verifier for the Erdős 536 proof."
    )
    parser.add_argument(
        "--section",
        action="append",
        choices=tuple(PAPER_SECTIONS),
        help="run only this paper-facing section; may be repeated",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="also run optional exhaustive small regressions",
    )
    parser.add_argument(
        "--list-sections",
        action="store_true",
        help="print available section names and exit",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.list_sections:
        for name in PAPER_SECTIONS:
            print(name)
        return

    print("Erdos 536 finite-arithmetic verifier")
    print(
        "Exact Fraction arithmetic and rigorous rational intervals; "
        "no binary floating point."
    )
    selected = args.section or list(PAPER_SECTIONS)
    for name in selected:
        PAPER_SECTIONS[name]()
    print("\nVerification completed successfully.")
    if args.self_test:
        run_self_tests()


if __name__ == "__main__":
    main()
