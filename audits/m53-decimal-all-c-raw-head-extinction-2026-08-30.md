# Decimal Setter All-`D_c` Raw-Head Extinction Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no lawful decimal-unit two-`c` raw head enters a later multi-role pole through an
all-`D_c` block of length at least three

This audit removes an infinite family from the initial distinguished-reset corridor. It applies
only to the first raw head. Later carrier numerators are generalized product residuals, so the
result does not prove arbitrary-depth projective avoidance or settle `M₅(3)`.

## Exact Objects

Fix deletion width `β≥2`, put `ρ=10^β`, and let an all-`D_c` block have upper length `n≥3`
and `q=10^n`. Every lawful decimal-unit two-`c` raw head has the digit word

```text
1^(β+2−s) 0^s,                 1≤s≤β−1,
```

where digit `1` means decimal `5`, digit `0` means decimal `7`, and its integer code `H`
satisfies

```text
9H=5·10^(β+2)+2·10^s−7.                              (1)
```

The compiler prefix proof is exact. The first `β` digits after the two initial `c` letters are
a nonempty run of ones followed by zeros. A zero-length final run would make the entire head a
string of decimal fives, contradicting that `H` is a `5`-adic unit. This yields the stated
range for `s`, including both endpoints.

For the setter constants, the all-`D_c` upper and lower codes `P,V`, trace `T`, and raw-head
residual `R` obey

```text
9μ=52ρ−7,                 E=18ρ−63,               G=502ρ−7,
9P=50ρq+2ρ−7,             9V=7q−7,
T=EP+GV,                  R=HT−10μGV.              (2)
```

The last identity uses the initial carrier denominator `D=1`; multiplication order was checked
against `peeledNumerator H 1 μ G T V`.

## Uniform Decomposition

Expanding (2), without division or positivity assumptions, gives integers `A,B` such that

```text
81R=10(441H+343)+qA+ρB.                              (3)
```

Explicitly,

```text
A=8100Hρ²+3276Hρ−441H−1827280ρ²+271460ρ−3430,
B=324Hρ−33894H+1827280ρ−271460.
```

Thus, for every `k≤min(n,β)`, equation (3) implies

```text
81R ≡ 10(441H+343)  (mod 10^k).                      (4)
```

Substituting (1) produces the decisive factorization

```text
441H+343=10^s(245·10^(β+2−s)+98).                   (5)
```

For `s≤β−2`, write the parenthesis in (5) as `K`. It is even and not divisible by five, and
(3) becomes

```text
81R=10^(s+1)K+10^n A+10^β B.                        (6)
```

A following multi-role pole requires the exact shell
`(ν₂(R),ν₅(R))=(n−1,n−1)`. Equation (6) contradicts it in every relative position:

- if `n≤s+1`, every term is divisible by `2^n`, whereas the shell forbids this;
- if `n=s+2`, the extra factor two in `K` gives the same contradiction;
- if `n≥s+3`, the shell supplies `5^(s+2)∣R`, and cancellation of the two error terms in
  (6) forces `5∣K`, contradicting (5).

The middle equality `n=s+2` is therefore not lost between the two off-boundary inequalities.

## First-Head Boundary

At the remaining endpoint `s=β−1`, the leading term in (6) cancels more deeply. Set
`a=10^(β−1)`, so `ρ=10a`. Direct elimination of `H` gives

```text
45R=q(250100ρ³−917504ρ²+135779ρ−1715)
   +ρ²(10004ρ−31514).                                (7)
```

The final parenthesis `10004ρ−31514` is not divisible by five. If `n≤2β`, both terms in (7)
are divisible by `2^n`, contradicting `ν₂(R)=n−1`. If `n>2β`, the required `5`-adic shell,
together with the factor five in `45`, forces one more factor of five into the second
parenthesis, again a contradiction. This includes `β=2`, `n=3`, and both sides of `n=2β`.

## Master Delta

Every all-`D_c` block of length at least three is now absent from the initial raw two-`c`
transition grammar. Together with `MM-S18`, this exhausts all admissible lengths for that
non-singleton family. It does not apply to a later generalized carrier, a rule-bearing or
`D_b`-containing block, or a transition into a singleton target. Those are the surviving
branches.

## Verification

`peeledDoubleCHead_unit_shape` checks the complete raw-head grammar and equation (1).
`allCDeletion_residual_decomposition`, `regularHead_decimalShell_impossible`, and
`exceptionalHead_decimalShell_impossible` check (3) through (7), including the boundary
splits. `allCDeletion_peeledDoubleCHead_shell_impossible` composes the grammar with both
arithmetic branches. The narrow module build, Lean language-server diagnostics, namespace
lint, and selected transitive axiom snapshots pass without warnings, suppressions, or proof
apertures.

## Artifacts

- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s19-all-deletion-raw-head-extinction)
- [`m53-decimal-recursive-carrier-2026-08-30.md`](m53-decimal-recursive-carrier-2026-08-30.md)
