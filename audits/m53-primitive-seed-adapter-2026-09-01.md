# M₅(3) primitive empty-front seed audit

## Boundary

This audit normalizes the `MM-O29` empty-front antecedent and substitutes it into the `MM-S89`
raw and primitive pullback criteria. It does not classify physical predecessor words, establish
encoded-entry reachability, or prove a pole.

## Primitive seed

Put `s=3^(β−1)`, `H=5·3^β−1=2h`, and let `U` be the natural swapped ternary target code. The
public `MM-S87` cores `B(s,U)` and `C(s,U)` are positive on every physical target. Lean proves

```text
X=(2HB+C)/(2B).
```

For `g₀=gcd(C,2B)`, define

```text
N=(2HB+C)/g₀,
D=2B/g₀.
```

Then `g₀` is the complete raw gcd, `g₀N=2HB+C`, `g₀D=2B`, `gcd(N,D)=1`, and `X=N/D`.

## Target-code gcd

The polynomial identities

```text
625B−162(U−4) ≡ 0  (mod H),
25C+27B ≡ 0        (mod 2H)
```

and `gcd(h,15)=1` give the exact common support

```text
d=gcd(h,2(U−4)),
gcd(h,B)=gcd(h,C)=gcd(h,g₀)=d.
```

For the primitive numerator, Lean proves the sharp uniform bound

```text
gcd(h,N) ∣ d.
```

Uniform coprimality is false. At offset six, width seven, target `cccccbc` has
`U=43017209`, `h=5467`, `g₀=616`, `d=77`, and `gcd(h,N)=7`. Another physical target at the same
width, `ccbcbbc`, has `U=1818720109804679` and `gcd(h,N)=11`. These are exact integer computations
used to reject a stronger claim; the formal theorem records the valid divisibility bound.

## Pullback criteria

Substitution into `MM-S89` gives

```text
h∣Nraw ↔ h/gcd(h,N)∣P,
h∣Nraw → h/d∣P.
```

If `Nraw=h·r₀`, the exact post-cancellation condition is

```text
h∣primitive(Nraw,Draw)
  ↔ gcd(h,Draw/gcd(r₀,Draw))=1.
```

All coordinates in these theorems are expanded from `U`; the residual gcd is not silently
dropped.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterPrimitiveSeedAdapter.lean`](../MatrixMortality/SwappedSetterPrimitiveSeedAdapter.lean).

The source compiles without warnings. Its namespace passes the default linters; every public
theorem is listed in `AxiomAudit.lean`; the reviewed axiom snapshot uses only standard axioms;
and the aperture scan is empty.

## Authorship

GPT-5.6 Sol, elicited by @eternalism_4eva.
