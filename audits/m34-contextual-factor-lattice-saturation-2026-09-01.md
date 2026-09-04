# M₃(4) Contextual Factor-Lattice Saturation Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `c9e3e4a` on `wave3-m34-transverse`
**Certificate:**
[`certify_mixed_prime_factor_lattice.py`](../tools/certify_mixed_prime_factor_lattice.py)

## Verdict

No nonconstant additive statistic built from factors of one fixed width `2≤r≤6` is invariant
under the mixed-prime quotient. This already holds for each of the five base kernel relations
separately.

For a binary word `w`, let `Φᵣ(w)∈Z^(2^r)` be its vector of overlapping length-`r` factor
counts. For one base relation `U=V`, define the contextual move lattice

```text
Λᵣ(U,V)=span_Z { Φᵣ(P·U·Q)−Φᵣ(P·V·Q) : P,Q∈{D,T}* }.
```

The certificate proves, in each of twenty-five relation/width cells,

```text
Λᵣ(U,V) = { z∈Z^(2^r) : Σz=0 }.
```

The right side is the augmentation lattice. Equality is integral and saturated, not merely
equality after tensoring with the rationals or reduction modulo selected primes.

## Finite Reduction

Internal factors of `P` and `Q` occur on both sides and cancel. Every surviving factor that
touches the left relation boundary sees only the last `r−1` letters of `P); every factor at
the right boundary sees only the first `r−1` letters of `Q`. A context shorter than `r−1`
must be retained whole. Thus the exact context state set is

```text
{ binary words of length at most r−1 },
```

of size `2^r−1`. Enumerating its square covers every arbitrary context pair. The base relation
words have length at least `27`, so no factor crosses both relation boundaries at the certified
widths.

Every contextual move has coordinate sum zero because the relation sides have equal length.
Deleting the final coordinate identifies the augmentation lattice with `Z^(2^r−1)`. The
certificate places every distinct projected move as a column of an integer matrix and computes
its exact column Hermite normal form. Identity HNF proves that the projected columns generate the
whole lattice with index one.

## Exact Census

| relation | `r=2` | `r=3` | `r=4` | `r=5` | `r=6` |
| --- | ---: | ---: | ---: | ---: | ---: |
| `r27` | 8 | 45 | 214 | 943 | 3,935 |
| `r29` | 8 | 45 | 215 | 943 | 3,934 |
| `r30a` | 8 | 45 | 214 | 943 | 3,935 |
| `r30b` | 8 | 45 | 214 | 942 | 3,933 |
| `r30c` | 8 | 45 | 217 | 945 | 3,938 |

Entries count distinct full contextual move vectors. The projected HNF in each column has
dimension and determinant

```text
r:                 2   3    4    5    6
augmentation rank: 3   7   15   31   63
HNF determinant:   1   1    1    1    1
```

A separate exact Gaussian elimination over `F₂,F₃,F₅,F₇` obtains the same full rank in every
cell. This modular check is redundant for saturation but independently catches rank or matrix
orientation errors. The canonical certificate digest is

```text
ee43620eb3cd33ef4558a89e0e8c593fb98b4beee5334983e76898f6792e0b47
```

## Linear Corollary

Let `A` be any abelian group and assign a weight `a_s∈A` to each binary length-`r` factor.
If

```text
Σ_s a_s Φᵣ(P·U·Q)_s = Σ_s a_s Φᵣ(P·V·Q)_s
```

for every `P,Q`, then the weight homomorphism kills `Λᵣ(U,V)`. Since this lattice contains
every difference of two standard basis vectors, all `a_s` are equal. The score is only that
common weight times the number of length-`r` factors, hence carries no quotient information
beyond length.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Boundary words of length at most `r−1` exhaust arbitrary contexts | promoted | direct factor locality |
| Each projected move lattice has full rational rank | promoted | exact HNF and four modular ranks |
| Each projected move lattice has integral index one | promoted | identity integer HNF |
| Every one-width additive invariant for `2≤r≤6` is trivial | promoted | augmentation-lattice duality |
| A mixture of several widths is trivial | open | cross-width cancellation was not classified |
| Every nonlinear or stateful short-factor invariant is trivial | rejected | not implied; `G3-S31` itself uses nonlinear fibre membership |
| The same saturation holds for `r≥7` | open | outside the certificate |
| The finite quotient has no multi-window fork | open | saturation kills an invariant method, not the target witness |
| `M₃(4)` follows | rejected | the quotient and terminal converse remain open |

## Master Delta

```text
DEAD: additive translation-invariant factor-count separation at each single width 2 through 6.
LIVE: nonlinear/stateful quotient invariants; mixed-width or longer-memory structure; new kernel
      relations; nonlocal terminal routing; arbitrary-word converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The PEP 723 certificate pins SymPy `1.14.0`. It recomputes the complete contextual move sets,
exact identity Hermite forms, four independent modular ranks, row hashes, and the canonical
payload digest. Ruff, formatting, and ty pass. No Lean source or axiom surface changes.
