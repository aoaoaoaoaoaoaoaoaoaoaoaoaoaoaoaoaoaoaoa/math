# Six-State Sandwich Saturation Audit

**Date:** 2026-07-25
**Target:** internal-word minimization of established `M₆(3)` families
**Verdict:** canonical paired-binary family uniformly full-algebra; all literal CHHN benchmark
packings computationally full-algebra

This audit applies the internal-word sandwich compiler `MM-C04` to the two canonical
six-dimensional, three-generator routes. It proves that the paired-binary mortality family
cannot shrink exactly. The CHHN result is a bounded modular computation only.

## Paired-Binary Mortality Family

Let `A₀,A₁` be the transposes of the six-state matrices in `PairedBinary.lean`. Put

```text
C=(μ,−1,3ρ,0,0,0)ᵀ,      L=(1,0,0,0,0,0),
P=CL,
ρ=3^β,                    μ=(5ρ−1)/2.
```

Write

```text
V=ternaryCode(nearyLower β body (rule c)),
B=3^(nearyLower β body (rule c)).length.
```

The mortality family is `{A₀,A₁,P}`. Its sandwich around the physical rank-one generator `P`
is the scalar series

```text
f(w)=LA_wC.
```

### Reachability

The six columns named by

```text
ε, 0, 1, 00, 10, 000
```

are

```text
C, A₀C, A₁C, A₀²C, A₁A₀C, A₀³C.
```

Their determinant is

```text
(81/2)ρ²(ρ−3)²(17B−18V+18ρ−33).                 (1)
```

The lower word for rule `c` ends in the binary suffix `10`. Under the nonzero ternary digit
encoding this gives

```text
V≡7 mod 9.
```

Its length is at least two, so `B≡0 mod 9`; moreover `ρ≡0 mod 9` for `β≥3`. The final factor
in (1) is therefore

```text
17B−18V+18ρ−33 ≡ 3 mod 9.
```

It is nonzero. The other factors are nonzero for `ρ≥27`, so the reachable space is all of
`ℚ⁶`.

### Observability

The six rows named by

```text
ε, 0, 1, 00, 01, 000
```

are

```text
L, LA₀, LA₁, LA₀², LA₀A₁, LA₀³.
```

Their determinant is

```text
18(15ρ+1)
(45Vρ²−372Vρ−25V−1125ρ²+3300ρ+1825).          (2)
```

Every term in the second factor containing `ρ` vanishes modulo nine. Since `V≡7 mod 9`,

```text
−25V+1825 ≡ 3 mod 9.
```

The second factor is nonzero, and so is (2). The representation is observable.

### Full Algebra

For each reachable word `u` and observable word `v`,

```text
A_uPA_v=(A_uC)(LA_v).
```

The six reachable columns and six observable rows are bases. Their thirty-six outer products
therefore span `M₆(ℚ)`:

```text
span_ℚ{A_w : w∈{0,1,P}*}=M₆(ℚ).
```

For every nonzero internal word `E=UW`, the reachable space of `WA_wU` is all of `ℚ⁶` and its
unobservable subspace is zero. By `MM-C04`, every internal-word sandwich has exact realization
dimension six. The canonical paired-binary family cannot prove `M₅(3)` by any exact invariant
subquotient.

## Literal CHHN Packings

For `d=3`, `h=k=2`, CHHN's trade assigns the five source matrices to

```text
U, X₁₁, X₁₂, X₂₁, X₂₂
```

and emits

```text
V₀=[[0,U],[I,0]],
V₁=[[X₁₁,X₁₂],[0,0]],
V₂=[[X₂₁,X₂₂],[0,0]].
```

At `β=3`, `body=bb`, the audit enumerated all `5!=120` assignments of the four nonsingular
payloads and rank-one separator to these slots. For each assignment it closed the word-product
span over `𝔽₁₀₀₀₀₀₃`. Every span had dimension `36`.

A full-dimensional modular span proves full algebra over `ℚ` for each concrete benchmark
packing. It does not prove uniformity in `β` and `body`. No registry theorem is promoted from
this finite computation.

## Reproduction

[`tools/audit_six_state_sandwich.py`](../tools/audit_six_state_sandwich.py) verifies the two
symbolic determinant identities and the 120 modular algebra closures. Its single `ty`
suppression is permitted for the same PEP 723 module-discovery limitation documented by the
ten-state audit.

## Consequence

The canonical paired-binary `M₆(3)` family is closed under exact sandwich minimization. Every
literal CHHN packing is already full-algebra on the benchmark. The `M₅(3)` campaign should not
spend further effort on exact subquotients of these families unless a new packing changes the
physical algebra.
