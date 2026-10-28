#!/usr/bin/env python3
"""Exact proper-subfield obstructions to UniformSubgroupWickBudget.

The named R389 predicate quantifies over every finite field and every torsion
subgroup.  For F=GF(s^2), H=GF(s)^*, d=s-1, the exact r-fold additive energy is
E_r=(d^(2r)+d)/s.  Thus its DC numerator is d^(2r+1)+s*d, not merely a large
raw zero-frequency term.  This script certifies route depths without floats,
constructs the quadratic field for small anchors, independently enumerates
anchor torsion sets and additive convolutions, and gives exact failing constants.

It also checks the two canonical sponsor primes, but in quadratic extensions.
For H=mu_(2^30) in the prime subfield, Cauchy-Schwarz on the s possible sum values
gives E_r >= |H|^(2r)/s, hence DC >= (s-1)*|H|^(2r).  These are lower bounds, not
complete energy computations.  Nothing refutes the sponsor prime-field target.

For the full-subfield family, any nonnegative C satisfying the budget must
obey C >= (s-1)/(16*r): s <= exp(r), exp(1)^2 < 8, and (2r-1)!! <= (2r)^r
bound the right side by (16*r*C*d)^r, while the left side is at least d^(2r).
The positive r-th root gives d <= 16*r*C.  Moreover
ceil(log s) <= sqrt(s)+1 <= 2*sqrt(s) and s-1 >= s/2 for s>=2, so C >= sqrt(s)/64.
Arbitrarily large primes s rule out every absolute nonnegative C.  A negative
C already fails at s=17, r=3.  This is an analytic argument about the explicit
family, not a claim that this Python probe is a Lean proof of the quantifier.
"""

# Copyright (c) 2026 Hardyzyt. All rights reserved.
# Released under the MIT and Apache 2.0 licenses. See LICENSE-MIT and LICENSE.

from fractions import Fraction
from math import factorial, isqrt, prod
import json


N = 2**30
PRIME_ANCHORS = (17, 97, 257, 65537)
SPONSORS = (
    ("P1", N * (2**128 + 192) + 1, 3,
     303645430271030343624574566109998498685964493478),
    ("P2", N * (2 * 2**128 + 13) + 1, 37,
     192152681249815148642741928588691886362054863855),
)


def trial_prime(n):
    return n >= 2 and all(n % divisor for divisor in range(2, isqrt(n) + 1))


def exp_one_bounds(terms=40):
    lower = sum((Fraction(1, factorial(i)) for i in range(terms + 1)), Fraction())
    # Remaining terms are dominated by the first omitted term times a
    # geometric series with ratio 1/(terms+2).
    upper = lower + Fraction(terms + 2, (terms + 1) * factorial(terms + 1))
    assert upper * upper < 8
    return lower, upper


def route_depth(base_size):
    """Certify ceil(log(base_size^2)/2)=ceil(log(base_size)) exactly."""
    lower, upper = exp_one_bounds()
    for r in range(1, 256):
        if upper ** (r - 1) < base_size <= lower ** r:
            return r
    raise AssertionError("Taylor interval cannot separate this route depth")


def field_multiply(x, y, prime, nonsquare):
    a, b = x
    c, d = y
    return ((a * c + nonsquare * b * d) % prime, (a * d + b * c) % prime)


def field_power(x, exponent, prime, nonsquare):
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = field_multiply(result, x, prime, nonsquare)
        x = field_multiply(x, x, prime, nonsquare)
        exponent >>= 1
    return result


def small_field_torsion_check(prime, nonsquare):
    """Directly certify H=mu_(s-1) in GF(s)[Y]/(Y^2-nonsquare)."""
    torsion = {
        (a, b) for a in range(prime) for b in range(prime)
        if field_power((a, b), prime - 1, prime, nonsquare) == (1, 0)
    }
    assert torsion == {(a, 0) for a in range(1, prime)}


def direct_sum_counts(prime, depth):
    counts = [1] + [0] * (prime - 1)
    for _ in range(depth):
        next_counts = [0] * prime
        for source, count in enumerate(counts):
            for h in range(1, prime):
                next_counts[(source + h) % prime] += count
        counts = next_counts
    return counts


def integer_failure_boundary(dc, budget_unit, depth, upper):
    """Return adjacent integer C values, first failing and second passing."""
    assert dc > 0 and budget_unit > 0 and depth > 0
    assert budget_unit * upper ** depth >= dc
    low, high = 0, upper
    while low + 1 < high:
        middle = (low + high) // 2
        if budget_unit * middle ** depth < dc:
            low = middle
        else:
            high = middle
    assert budget_unit * low ** depth < dc <= budget_unit * high ** depth
    return low, high


def full_subfield_certificate(s):
    assert trial_prime(s)
    d, q, r = s - 1, s * s, route_depth(s)
    nonsquare = next(x for x in range(2, s) if pow(x, d // 2, s) == s - 1)
    # The quadratic is irreducible because nonsquare has Legendre value -1.
    if s <= 257:
        small_field_torsion_check(s, nonsquare)
    # z,w count sums equal to zero and to any one fixed nonzero element.
    z, w = 1, 0
    for _ in range(r):
        z, w = d * w, z + (d - 1) * w
    assert z + d * w == d ** r
    assert z == (d ** r + d * (-1) ** r) // s
    assert w == (d ** r - (-1) ** r) // s
    if s <= 257:
        assert direct_sum_counts(s, r) == [z] + [w] * d
    energy = z * z + d * w * w
    assert s * energy == d ** (2 * r) + d
    dc = q * energy - d ** (2 * r)
    assert dc == d ** (2 * r + 1) + s * d
    wick = prod(range(1, 2 * r, 2))
    unit = q * wick * d ** r
    failure, passing = integer_failure_boundary(dc, unit, r, d)
    fails_reference = dc * 2 ** r > unit * 7 ** r
    if s >= 97:
        assert fails_reference
    # Independent exact check of the coarse algebraic lower bound.
    assert unit * Fraction(d, 16 * r) ** r < dc
    return {
        "subfield_size": s,
        "quadratic_nonsquare": nonsquare,
        "ambient_field_size": q,
        "torsion_order": d,
        "route_depth": r,
        "largest_integer_C_failing": failure,
        "smallest_integer_C_passing": passing,
        "fails_C_7_over_2": fails_reference,
        "DC_formula": "(s-1)^(2r+1)+s*(s-1)",
        "coarse_necessary_C_lower_bound": str(Fraction(d, 16 * r)),
        "scope": "Exact energy of a proper-subfield multiplicative group.",
    }


def sponsor_extension_certificate(name, s, base, g):
    # Existing main Lean modules supply the primality certificates.
    assert pow(base, (s - 1) // 2, s) == s - 1
    assert pow(base, (s - 1) // N, s) == g
    assert pow(g, N, s) == 1 and pow(g, N // 2, s) == s - 1
    q, r = s * s, route_depth(s)
    # Sums of r subgroup elements stay in GF(s), so Cauchy-Schwarz gives
    # s*E_r >= N^(2r). Clearing the ambient q=s^2 normalization gives this.
    dc_lower = (s - 1) * N ** (2 * r)
    unit = q * prod(range(1, 2 * r, 2)) * N ** r
    failure, passing = integer_failure_boundary(dc_lower, unit, r, N)
    assert dc_lower * 2 ** r > unit * 7 ** r
    return {
        "prime_subfield": name,
        "subfield_size": s,
        "ambient_field_size": q,
        "quadratic_nonsquare": base,
        "torsion_order": N,
        "route_depth": r,
        "largest_integer_C_refuted_by_lower_bound": failure,
        "first_integer_C_not_refuted_by_this_lower_bound": passing,
        "fails_C_7_over_2": dc_lower * 2 ** r > unit * 7 ** r,
        "DC_lower_bound": "(s-1)*N^(2r)",
        "scope": "Sponsor prime embedded in its quadratic extension; lower bound only.",
    }


def main():
    result = {
        "target": "R389WickBudgetSupBound.UniformSubgroupWickBudget",
        "exact_subfield_groups": [full_subfield_certificate(s) for s in PRIME_ANCHORS],
        "sponsor_quadratic_extensions": [sponsor_extension_certificate(*x) for x in SPONSORS],
        "status": "PASS",
        "production_prime_field_target": "OPEN",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
