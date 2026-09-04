# M₃(4) Mixed-Prime Macro-Address Comparator Audit

**Date:** 2026-08-31
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `49c6465` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimeMacroComparator.lean`](../MatrixMortality/MixedPrimeMacroComparator.lean)

## Verdict

The free `{DT,TD}` affine stack from `G3-S16` has an injective one-coordinate code: evaluation at
zero recovers every finite address, including its length. No separate clock is needed if the
terminal interface can compare these scalar offsets.

Two equal-length addresses also commute if and only if they are identical. More strongly, for
every raw mixed-prime toggle word `Z`, the reduced `bcbc` fork

```text
V Z U V U = U Z V U V
```

holds as an equality of affine actions if and only if the equal-length addresses `U,V` are
identical. The toggle may be empty or nonempty and otherwise arbitrary. This supplies the missing
comparator algebra in the mandatory five-factor shape.

The five-factor theorem assumes equal macro length. The direct offset reader does not. Neither
supplies a complete `M₃(4)` compiler: the endpoint construction must dynamically produce and
compare the two addresses without identifying its fixed data controls or admitting malformed
raw control words.

## Global Offset Code

For a nonempty address of length `n`, `G3-S16` gives

```text
offset(w)=code(w)/(3·5^(n-1)).
```

Appending the final digit gives

```text
code(wb) ≡ digit(b)·2^n (mod 5),       digit(b)∈{2,3}.
```

Thus `5∤code(w)` for every nonempty address. If two offsets agree, clearing denominators yields

```text
code(u)·5^|v| = code(v)·5^|u|.
```

Exact divisibility forces `|u|=|v|`; otherwise one unit-mod-five code would be divisible by five.
The fixed-length radix theorem then gives `u=v`. The empty address is the unique address with
offset zero because every nonempty offset is positive.

Lean formalizes the modular unit, cleared cross equation, exponent cancellation, positivity, and
global injectivity. In particular,

```text
w ↦ wordAction(expandAddress(w),0)
```

is injective. This is a scalar reader for arbitrary lengths, not merely a length-plus-offset pair.

## Scalar Factorization

Let two length-`n` addresses act as

```text
U(t)=rt+u,       V(t)=rt+v,       r=(2/5)^n,
```

and let the toggle act as `Z(t)=ct+d`. Every raw toggle has `0<c≤1`. At `t=0`, the commutator
difference is

```text
U(V(0))-V(U(0)) = (1-r)(u-v).
```

For `n>0`, `0<r<1`; hence commutation is equivalent to `u=v`.

The five-factor difference is

```text
VZUVU(0)-UZVUV(0) = (u-v)(cr³-cr²+cr-1).
```

Put `f(r)=r³-r²+r`. Then

```text
1-f(r)=(1-r)(1+r²)>0,
```

so `0<f(r)<1`. Since `c≤1`, the second factor satisfies `cf(r)-1<0`. It cannot vanish, and the
five-factor equality is again equivalent to `u=v`. For `n=0`, both addresses are empty.

`G3-S16` proves fixed-length injectivity of the mixed radix offset, so `u=v` is equivalent to
literal equality of the binary macro addresses.

## Formal Boundary

Lean proves the following interfaces:

| Interface | Meaning |
| --- | --- |
| `wordScale_expandAddress` | address multiplier is exactly `(2/5)^n` |
| `wordScale_expandAddress_eq_iff_length_eq` | equal multipliers are exactly equal macro lengths |
| `five_not_dvd_addressCode` | every nonempty address code is a unit modulo five |
| `addressOffset_injective_of_ne_nil` | cleared five-adic denominators recover nonempty addresses |
| `addressOffset_injective` | one scalar offset recovers every address, including empty |
| `expandAddress_at_zero_injective` | evaluation at zero is the corresponding scalar action reader |
| `expandAddress_commute_at_zero_eq_iff_of_length_eq` | one scalar commutator value compares equal-length addresses |
| `expandAddress_commute_iff_of_length_eq` | nested affine actions commute exactly at address equality |
| `wordAction_addressCommutator_at_zero_eq_iff_of_length_eq` | literal concatenations `UV` and `VU` compare at scalar state zero |
| `wordAction_addressCommutator_eq_iff_of_length_eq` | literal concatenations `UV` and `VU` agree exactly at address equality |
| `addressFork_at_zero_eq_iff_of_length_eq` | one nested five-factor scalar compares addresses for arbitrary `Z` |
| `addressFork_eq_iff_of_length_eq` | nested five-factor actions compare addresses for arbitrary `Z` |
| `wordAction_addressFork_at_zero_eq_iff_of_length_eq` | literal `VZUVU/UZVUV` words compare at scalar state zero |
| `wordAction_addressFork_eq_iff_of_length_eq` | literal `VZUVU/UZVUV` words compare addresses for arbitrary `Z` |

The proof uses the formal `G3-S16` action formula and fixed-length injectivity. Address length is
an exact multiplier clock by unique powers of `2/5`. The toggle slope bound is the formal
all-word mixed-prime contraction theorem, not a finite enumeration.

## Compiler Boundary

The five-factor comparator consumes two synchronized equal-length macro addresses. Its branches
contain each address twice, so their total slopes agree even when the address lengths differ;
unequal-length fork collisions remain possible. Explicitly, for `A=DT`, the nonempty addresses
`U=A`, `V=A²` and raw toggle `Z=A³` make both fork branches equal `A⁹`. Their slopes are distinct,
but all three actions share `A`'s fixed point, so this witness lies on the already forbidden
centralizer diagonal. The direct offset reader has no equal-length restriction, but the compiler
must expose the difference of two evaluated offsets to its one terminal scalar.

The comparator also cannot be installed by setting the fixed `b` and `c` core maps equal. Exact
endpoint semantics requires distinct data maps and rejects the resulting common-fixed collapse.
The live construction must generate `U,V` dynamically inside a guarded source spelling, enforce
equal macro length, then route the five-factor comparison to the terminal scalar. This is a
source/interface obligation, not a missing equality test.

The natural successor is now sharper: route two dynamically produced address offsets to the
terminal difference functional, or force equal-length production and use the five-factor fork.
A complete converse must also reject every malformed raw word outside the address grammar.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Address multiplier equality is equivalent to address-length equality | promotion | Lean theorem |
| One scalar offset is injective on arbitrary finite addresses | promotion | Lean five-adic denominator theorem |
| Equal-length macro addresses commute exactly when equal | promotion | Lean theorem |
| The reduced five-factor fork compares equal-length addresses for every raw toggle | promotion | Lean factorization and contraction bound |
| The five-factor comparator infers equal address length | rejected | explicit hypothesis; unequal-slope fork collisions exist |
| The fixed data controls may be identified to invoke the comparator | rejected | existing endpoint distinctness/common-fixed obstruction |
| Dynamic address production and malformed-word rejection are complete | open | no serializer/converse theorem |
| `M₃(4)` follows | rejected | synchronized production or two-offset routing and the all-word converse remain |

## Master Delta

```text
STACK: free binary `{DT,TD}` affine addresses.
SCALAR CODE: evaluation at zero is globally injective, including address length.
FORK COMPARATOR: exact inside `UV=VU` and `VZUVU=UZVUV` at equal length.
MISSING: dynamic two-offset routing or synchronized fork production, plus arbitrary-word converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, and forbidden-aperture scan pass. The formal source SHA-256 is

```text
179ddec206e9011af2e5f01f215410a3c8b3a0624ab13e06cce58862922e3706  MixedPrimeMacroComparator.lean
```
