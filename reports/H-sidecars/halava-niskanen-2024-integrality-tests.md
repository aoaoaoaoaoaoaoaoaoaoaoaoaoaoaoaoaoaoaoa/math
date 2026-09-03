# Halava and Niskanen (2024): On simulating Turing machines with matrix semigroups with integrality tests

**Citation.** Vesa Halava and Reino Niskanen, “On Simulating Turing Machines with Matrix
Semigroups with Integrality Tests,” *Theoretical Computer Science* 1005 (2024), 114637.

- Work identity: DOI 10.1016/j.tcs.2024.114637
- Canonical source: https://doi.org/10.1016/j.tcs.2024.114637
- Inspected source: https://researchonline.ljmu.ac.uk/id/eprint/23352/1/On%20simulating%20Turing%20machines%20with%20matrix%20semigroups%20with%20integrality%20tests.pdf
- Local artifact: none; the prompt forbids adding the PDF to `references/`
- Version and status: published version; peer-reviewed; CC BY 4.0
- Retrieved: 2026-09-02
- Inspected PDF SHA-256: `6118292cd1be947b0df8466916f8bffe2ac0477ed31ca203b0e6c667a177a413`
- Synopsis basis: complete text and formula inspection of the 12-page published PDF

## Synopsis

The paper encodes the two tape halves in the lower row of a triangular `3×3` matrix. For
`C = (Q × Γ) ∪ Γ ∪ {#}`, it assigns each letter `aᵢ` the digit
`φ(aᵢ) = ∏_{j≠i} pⱼ`, where the `pⱼ` are distinct odd primes, and then uses an ordinary radix
`n > ∏ pⱼ`. A valid configuration has diagonal entries `n^{|u|}, n^{|v|}, 1` and lower entries
`σ(u), σ(v), 1`.

A right move has diagonal `(n,n⁻¹,1)` and a lower-right entry `−n⁻¹σ(d)`; a left move has
diagonal `(n⁻¹,n,1)` and a lower-left term containing `−n⁻¹σ(d(q,a))`. Correctly guessed
symbols cancel these denominators. Theorems 7 and 8 claim that an externally integral path
between designated configuration matrices exists exactly for a Turing computation. Theorem 11
adds three endpoint matrices and claims undecidability of the identity problem when every prefix
product is externally required to be integral.

## Denominator Audit

Every denominator is a power of the fixed radix `n`; the digit primes `pⱼ` occur only in
numerators. Thus the possible offending primes are the fixed finite set `{p : p ∣ n}`, not a
run-dependent set. Choosing the admissible radix to be a prime `n = π > ∏ pⱼ` isolates one
offending prime and makes every nonzero digit mismatch a `π`-unit.

For a valid right tape `σ(#(cv)ᴿ) = nσ(#vᴿ) + σ(c)`, choosing `d ≠ c` makes entry `(3,2)`

```text
n⁻¹(σ(#(cv)ᴿ) − σ(d)) = σ(#vᴿ) + (σ(c) − σ(d))/n,
```

of valuation `−1` when `n=π`. For a left move, a wrong scanned state-symbol pair analogously
appears in `(3,1)` as
`(σ((q,a)) − σ((q′,a′)))/n`. Boundary and identity-wrapper misuse can also expose denominators
in diagonal entries. In the generators themselves, the negative powers occur at `(1,1)` and
`(3,1)` for left moves, at `(2,2)` and `(3,2)` for right moves, and throughout `N₂,N₃`.

The ordinary right and left generators have determinant `1`, but are not entrywise
`π`-integral. The right-border insertion and special left removal have determinants `n` and
`n⁻¹`; the endpoint matrices `N₁,N₂,N₃` have determinants `n⁵,n⁻¹,n⁻⁴`.

## Poison Falsifier

The negative valuation is not forward-invariant. If the bad right-pop coordinate is
`t + (c-d)/π`, the next left push sends it to

```text
π(t + (c-d)/π) + b = πt + c - d + b ∈ ℤ.
```

An exact instance with `π=101` gives

```text
C = [[10201,0,0],[0,10201,0],[1222,5063,1]],
R = [[101,0,0],[0,1/101,0],[121,-17/101,1]],
L = [[1/101,0,0],[0,101,0],[1899/101,14,1]],
C R = [[1030301,0,0],[0,101,0],[123543,5046/101,1]],
C R L = [[10201,0,0],[0,10201,0],[1242,5060,1]],
det R = det L = 1.
```

These are the paper's right-then-left affine forms: the first product is nonintegral and the
second is integral. Conjugation cannot put either radix pop into `GL₃(ℤ_π)`, since its triangular
spectrum contains `π⁻¹`; scaling away the denominator makes the determinant nonunit. A separate
monotone poison coordinate or a non-radix simulation is therefore required before `MM-C01` can
internalize the external test.

A fixed finite alphabet of unary rational weights would also have bounded denominator primes,
but boundedness is already achieved here and does not prevent healing. Position-indexed prime
weights would instead introduce run-dependent primes. Any unary encoding retaining mutually
inverse `π`-dilation and `π`-contraction retains this obstruction.

## Source Assessment

Lemma 6 is false as stated. It permits arbitrary `α = ∑ zᵢσ(sᵢ)` with integral coefficients,
yet taking `α = σ((q,a)) - σ(b) + σ(c)` makes its forbidden equation hold identically. This can
also satisfy the proof's needed condition that `α` is not a letter image: with digit primes
`3,5,7` (and any common product `S` of further primes), the three images are `35S,21S,15S`, while
`α=29S` is not any image and

```text
29S - 35S + 21S = 15S.
```

Lemma 5 invokes Lemma 6, and Theorems 7, 8, and 11 invoke Lemma 5. The paper may have intended an
additional ancestry restriction on coefficients reachable from an invalid simulation, but none
is stated or proved. No correction or erratum was found as of the retrieval date. The published
undecidability claims should therefore be treated as proof-obstructed, not established, pending
a repaired invariant.
