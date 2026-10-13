# Exact first-sponsor bracket

Author: Mikhail Izhutkin (@mashingaan)

## Instance and evidence pins

The code is `evalCode g 1073741824 536870911`, equivalently the dimension
`536870912` Reed-Solomon code on the injective domain `i ↦ g^i`.

- Prime `P = 365375409332725729550921208179070755120141565953`
- Generator `g = 303645430271030343624574566109998498685964493478`
- Length `n = 1073741824`
- Target error `epsStar = 1/340282366920938463463374607431768211456`
- Threshold object `MCAThresholdLedger.mcaDeltaStar`, a supremum of good radii

The attained-maximum sponsor formulation remains a separate equivalence obligation.
This investigation does not assume an equivalence merely from shared notation.

The frontier was read at these exact heads:

| PR | Head | Relevant content |
| --- | --- | --- |
| 222 | `f5cbee0fab99dce92f17091402dc6a04ed998d86` | Common-factor upper constructions and earlier canonical ceiling |
| 223 | `01811c0937d2f9d0fbdecefbcbe7021e0876fd4e` | One-way BCHKS bridge and exact production interface no-go results |
| 224 | `d7551e4c651f092ee75c42591ece6389a6181a63` | Canonical triple-incidence floor |

## Current bounds

The axiom-clean lower bound from PR 224 is

`210683556/1073741824 ≤ mcaDeltaStar C epsStar`.

Its full hosted validation passed at the pinned head in
[run 38366369251](https://github.com/SlopDotCash/proximityprize/actions/runs/38366369251).

The full-scale construction in PR 222 gives the candidate ceiling

`mcaDeltaStar C epsStar ≤ 178956971/536870912`.

Its compressed exact arithmetic and algebraic derivation are public. The new Lean
module `_IncidenceFullScaleCores.lean` attempts the complete canonical transfer.
Until its kernel check passes, the latter rational is computational/algebraic
evidence rather than a new kernel-checked threshold bound.

The prospective interval width is exactly

`147230386/1073741824 = 73615193/536870912`.

No matching threshold or prize closure is claimed.

The weighted-line continuation gives the candidate lower bound

`214719988/1073741824 ≤ mcaDeltaStar C epsStar`.

Its integer budget passed independently in
[hosted run 38371632111](https://github.com/mashingaan/proximityprize/actions/runs/38371632111)
at `8122f9b281ca0aa77d3229f6c2275af5abb94022`.
This is `4036432` Hamming steps above PR 224. The production Lean transfer is
`IncidenceCanonicalWeighted.firstPrime_weighted_floor` and is not yet kernel verified.
Together with the full-scale ceiling, its prospective bracket width is
`143193954/1073741824 = 71596977/536870912`.

The continuation retains the cube moment and improves the lower union mass.
On every canonical witness line, choose one private agreement coordinate per
head. They are distinct, and the error union of any two distinct heads contains
all of them. Thus a line of size `ell` contributes deficit at most `d+1-ell`
per distinct triple, rather than `d+1`. No extra RS hypothesis is introduced.
The weighted line function `ell^2*(d+1-ell)` is nondecreasing up to the cap
`b=t+1` under `3b≤2(d+1)`, which holds at the literal production parameters.

The improved weighted budget is

`s*Deficit ≤ s*m*b^2*(d+1-b) + (d+1)*(3m^3+s^2*m^2)`.

Repeated-index tuples retain the safe `3m^2` penalty. The exact optimized
production values are `t=214719987`, `s=56756`, with strict integer slack
`84086556016907437521639365648630530087415504642500`.
At `t=214719988` the slack is
`-77933888686913623791819247124213472026898589548800`.
These computations certify the displayed inequality, pending its Lean derivation.

## Construction audit

Let `c = 536870910`, `a = 178956971`. Partition coordinates into the common
initial segment of size `c`, three consecutive groups of size `a`, and one
leftover coordinate. Assign group heights `0,1,2` and leftover height `3`.
The common coordinates can also have height `3`, because the locator vanishes there.

Let `Z(X) = ∏_{i<c}(X-g^i)`. The received rows are
`u1(i) = h(i) Z(g^i)` and `u0(i) = h(i)^2 g^i Z(g^i)`.
For group `j` use `v1 = j Z` and `v0 = j^2 X Z`.

The maximum degree is `c+1 = 536870911`, strictly below the dimension.
Each core has `c+a = 715827881` coordinates, at least the dimension.
For every coordinate `x` outside core `j`, the scalar
`gamma(j,x) = -(h(x)+j) g^x` gives agreement on core `j` plus `x`.
The exact support size is `715827882`, so the closed agreement inequality
holds at radius `178956971/536870912`.

Canonical nonjointness follows from interpolation uniqueness on the core.
Any putative row-1 codeword explaining the full witness must equal `j Z`,
which disagrees at `x` because both `h(x)-j` and `Z(g^x)` are nonzero.

The scalar coefficients lie in `{1,2,3,4,5}`. Their `n`-th powers modulo `P`
are pairwise distinct. A scalar collision therefore forces equal coefficients,
then equal coordinates by generator injectivity, then equal group indices.
This gives `3(n-c-a) = 1073741829 = n+5` distinct bad scalars.

The exact normalized error comparison is strict:

`1073741829 * 340282366920938463463374607431768211456 - P`
`= 1701411834604692317316873036952682627071 > 0`.

Thus the event mass exceeds `epsStar`, not merely its floor approximation `n/P`.
`mcaDeltaStar_le_of_bad` converts that strict error inequality into a non-strict
threshold ceiling at the bad radius. It does not assert goodness at the ceiling.

The full support claim uses the factorization
`w_j - (u0+gamma*u1) = (j-h) Z ((j+h)X+gamma)`.
Outside the core the first two factors are nonzero. Two further roots would
give a scalar collision, which the coefficient-power certificate excludes.
This claim concerns the designated head, not every possible alternative head.

## Finite extremal problem behind PR 224

Fix `m = 1073741825` distinct scalar parameters `gamma_i` and heads `w_i` in
a vector subspace `C` over the prime field. Let the coordinate set have size
`n = 1073741824`. Every witness has agreement set `T_i` and error set
`E_i = T_i^c`, with `|E_i| ≤ t`.

There are received rows `u0,u1` such that on `T_i`,
`w_i = u0 + gamma_i*u1`. No pair of elements of `C` jointly explains these
two received rows on `T_i`.

The only code-distance assumption used is that a codeword supported on at most
`d = 536870912` coordinates is zero. Consequently, a triple with error union
of size at most `d` lies on one affine head line. Every pair of distinct scalar
parameters determines its unique head line. A line contains at most `b = t+1`
witnesses, by the private-coordinate argument and canonical nonjointness.

The extremal question is whether such a family can exist. The RS wrapper is
needed to instantiate the support-distance assumption, not to evaluate the
remaining finite inequalities.

## Moment identities and finite budgets

After padding errors to size `t`, let `a_x` count witnesses agreeing at coordinate
`x`. For ordered tuples with repetition,

`U_r = sum_{i_1,...,i_r} |E_{i_1} union ... union E_{i_r}|`
`= n*m^r - sum_x a_x^r`.

Also `sum_x a_x = m(n-t)`. Convexity gives

`n^(r-1) U_r + (m(n-t))^r ≤ n^r m^r`.

The number of tuples with exactly `j` distinct indices is
`StirlingSecond(r,j) * falling(m,j)`. Therefore the repeated-index contribution
is exactly `m^r - falling(m,r)`. Dropping all their nonnegative union masses
is safe but may lose information. This loss is explicit, not an optimality claim.

For `r≥3`, a distinct tuple with union size at most `d` is collinear, because
each triple is collinear and the line through a fixed pair is unique.
Peel whole lines of size at least an integer `s≥2`. A collinear tuple mixed
between the peeled line and its complement contains exactly one peeled point.
Its remaining coordinates determine that point, giving at most `r*m^(r-1)`
mixed tuples per peeled block. There are at most `m/s` blocks. The terminal
family has line occupancy below `s`, giving at most `m^2*s^(r-2)` distinct
collinear tuples. Within the peeled blocks, the line cap gives `m*b^(r-1)`.

The resulting conservative budget is

`s L_r ≤ s*m*b^(r-1) + r*m^r + s^(r-1)*m^2`.

Combined with the moment identity, a positive value of

`s*n^(r-1)*(d+1)*falling(m,r) + s*(m(n-t))^r`
`- s*n^r*m^r`
`- n^(r-1)*(d+1)*(s*m*(t+1)^(r-1)+r*m^r+s^(r-1)*m^2)`

excludes the family under this budget. For each order the independent probe
minimizes the strictly convex block cost over integers and searches the exact
largest admissible `t`. All calculations use integers and rational arithmetic.
Orders above three remain research derivations until formalized.

The independent arithmetic check passed in
[hosted run 38370208361](https://github.com/mashingaan/proximityprize/actions/runs/38370208361)
at `250f0876459990653a2bafee77450ddc88c7b2ce`.

| Order | Optimal integer block | Largest certified error count | Prospective lattice floor |
| --- | --- | --- | --- |
| 3 | 56756 | 210683555 | 210683556/1073741824 |
| 4 | 1321123 | 169941563 | 169941564/1073741824 |
| 5 | 6739646 | 138942677 | 138942678/1073741824 |
| 6 | 18194417 | 117144077 | 117144078/1073741824 |

The triple optimum selects block `56756`, one above the block used in PR 224.
This improves arithmetic slack but not its integer threshold. Exact repeated-index
partitions also leave that threshold unchanged.

There is an all-orders obstruction for this particular budget. If `r≥4` and
`t/n≥1/6`, dropping its nonnegative collinearity penalty and replacing
`falling(m,r)` by `m^r` bounds its normalized slack above by

`1/2 + 1/n + (5/6)^4 - 1 = 1/n - 23/1296 < 0`.

Thus no higher order in this budget can certify even `1/6`, whereas the triple
floor is strictly larger than `1/6`. Further blind iteration of this same budget
cannot improve the current floor. This is an optimization obstruction for the
displayed inequalities, not a countermodel to all canonical witness assumptions.

Increasing the order in this particular budget is not automatically a stronger
argument. Nor does failure of this budget establish a barrier for the full
canonical assumptions. A barrier still requires a countermodel or sharp
optimization certificate satisfying all extracted assumptions.

## Theorem map

| Bound or step | Assumptions | Evidence |
| --- | --- | --- |
| PR 224 floor `210683556/1073741824` | Exact sponsor code, canonical events, RS support distance | Axiom-clean Lean and full CI |
| Core sizes and locator degrees | Three finite coordinate embeddings and product degree bound | New Lean check pending |
| Nonjointness | Core size at least dimension, RS interpolation uniqueness, off-core nonzero factors | New Lean check pending |
| Scalar census | Exact generator order and five coefficient-power separations | Independent arithmetic, new Lean check pending |
| Candidate ceiling `178956971/536870912` | All construction steps and strict normalized mass | Canonical Lean transfer pending |
| Higher moment budgets | Line geometry, occupancy cap, support distance, exact repetitions, convexity | Reproducible research calculation pending hosted execution |

No refuted predecessor-cap, generic BGK estimate, or asymptotic Jeronimo
conclusion is used. Literature work will be restricted to a specific missing
finite structural lemma if this investigation identifies one.
