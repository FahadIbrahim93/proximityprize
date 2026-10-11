# Expanded production incidence cores

Author: Mikhail Izhutkin (@mashingaan)

Evidence class: exact computation and algebraic derivation. The new bounds below are not Lean formalized. They strengthen the computational lane of PR 222, not its existing kernel-checked three-core consumer.

## Construction and canonical event

Let n = 2^30, d = 2^24, k = 2^29. Use the certified generator g of order n in either canonical prize field. Put omega = g^d and Z(X) = product over b = 0,...,30 of (X^d - omega^b). Partition s*t of the remaining 33 labels into s disjoint groups of size t, and give group j height j for j = 0,...,s-1. Give any remaining labels height s.

For x = g^i of label i mod 64 define u1(x) = h(x)*Z(x) and u0(x) = h(x)^2*Z(x)*x. For group j use decoded heads v1 = j*Z and v0 = j^2*X*Z. Their degrees are at most 31d and 31d+1, both strictly less than k. Each head pair agrees with the received pair on the common 31 labels and group j, a core of (31+t)d coordinates.

At any coordinate x outside that core, h(x) differs from j and Z(x) is nonzero. Set gamma = -(h(x)+j)*x. The decoded codeword v0+gamma*v1 agrees with u0+gamma*u1 on the core and x, giving support size (31+t)d+1. This meets the canonical agreement threshold at delta = ((33-t)d-1)/n.

The support is not jointly explained: if any dimension-k RS head agreed with u1 on that support, its agreement on the core of at least k distinct coordinates would force it to equal j*Z. At x it cannot equal u1 because (h(x)-j)*Z(x) is nonzero. This negates the forall-support joint-head condition in Errors.mcaEvent. The witness support need not be the full exact agreement support.

## Distinctness and exact counts

For each fixed label the eligible coefficients h+j are pairwise distinct. Every coefficient is nonzero. Across different coefficients a and b, equality of scalars implies (a/b)^n = 1. The script checks a^n != b^n modulo the exact production prime, which excludes that collision. Within a fixed coefficient, generator injectivity distinguishes coordinates. Thus all s*(33-t)*d slots give distinct canonical bad scalars, without enumerating the production domain.

First field P = n*(2^128+192)+1, budget floor(P/2^128) = n:

- s = 3, t = 11, no leftover labels
- coefficient inventory {1,2,3}
- support size 704643073
- radius 369098751/1073741824 = 11/32 - 1/n
- bad-count lower bound 1107296256 = 66d
- budget excess 33554432 = 2d

Second field P = n*(2*2^128+13)+1, budget 2n:

- s = 5, t = 6, three leftover labels of height 5
- coefficient inventory {1,...,9}
- support size 620756993
- radius 452984831/1073741824 = 27/64 - 1/n
- bad-count lower bound 2264924160 = 135d
- budget excess 117440512 = 7d

The script independently cross-multiplies count*2^128 > P. Subject to the derivation above, MCAWitnessSpread and MCAThresholdLedger.mcaDeltaStar_le_of_bad would transfer these bad radii into the corresponding upper threshold bounds. That transfer has not been implemented or newly kernel checked for these expanded cores. No exact threshold or prize closure is claimed.

## Optimization scope and reproduction

The probe enumerates equal-size designs with common 31 labels, 3 <= s <= 33, t >= 1, s*t <= 33. It maximizes t subject to a strictly over-budget count. The maximal t is 11 in the first field and 6 in the second. This is optimal only within this family, not among arbitrary RS stacks.

Run `python scripts/probes/probe_incidence_expanded_cores.py`. All load-bearing arithmetic uses integers or Fraction. The script also independently reconstructs every witness over F_1409 with n = 128 and d = 2, using direct Lagrange interpolation rather than the symbolic head formula. The small instance verifies the construction implementation, while the explicit production modular-power certificates supply the production coefficient separation. Neither check replaces a Lean proof of the expanded construction.
