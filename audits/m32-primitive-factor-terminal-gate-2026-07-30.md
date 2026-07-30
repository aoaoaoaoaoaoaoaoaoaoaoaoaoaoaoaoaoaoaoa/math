# M₃(2) primitive-factor terminal gate

Date: 2026-07-30

## Finite-family theorem

For one integral guard step, let

```text
(m̃,ñ)=g(m′,n′)
```

and let `S` be a finite family of distinct primes dividing `pᵃ−1`. Every member obeys the exact
dichotomy

```text
ℓ∣g  or  ℓ∣m′−n′.
```

Distinct primes are pairwise coprime. If every prime in `S` were swallowed, their product would
divide `g`, hence divide `ñ=T(m,n)`. Therefore

```text
|T(m,n)| < ∏_{ℓ∈S} ℓ
```

forces either `T(m,n)=0` or a surviving factor with `m′≡n′ (mod ℓ)`.

## Canonical primitive family

Define

```text
S_a={ℓ : ℓ∣Φ_a(p), ℓ∤a}.
```

Every `ℓ∈S_a` is a primitive prime divisor of `pᵃ−1`; equivalently, `p` has exact order `a`
modulo `ℓ`. Its product is the primitive cyclotomic radical

```text
R_a=∏_{ℓ∈S_a} ℓ.
```

The terminal-defect estimate

```text
|T(m,n)|≤(|A−L|+|D|) max(|m|,|n|)
```

gives the checked implication

```text
R_a>(|A−L|+|D|)H
⇒
T=0 or some exact-order quotient sees a projective reset.
```

Equivalently, a nonterminal step which avoids every primitive reset satisfies

```text
R_a≤|T|≤(|A−L|+|D|)H.
```

## Strategic boundary

The local-global idea succeeds exactly up to a squarefree radical. A lower bound for the full
cyclotomic value `Φ_a(p)` is not enough: repeated powers of primitive primes contribute to the
value but not to the product of distinct finite quotients. Uniformly controlling this loss is
number-theoretic. The alternative is dynamical: show that at least one surviving exact-order
quotient excludes the terminal residue.

Thus the remaining fork is now sharp.

1. Prove a primitive-radical lower bound strong enough relative to the orbit height.
2. Prove completeness of the finite projective quotient sieve.
3. Construct a rational orbit that repeatedly swallows the primitive radical, thereby locating
   the hard Diophantine mechanism explicitly.

## Lean artifacts

- `ReturnGuard.primitiveCyclotomicPrimes`
- `ReturnGuard.primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes`
- `ReturnGuard.terminal_or_exists_cyclotomic_reset`
- `ReturnGuard.cyclotomicProduct_le_terminalDefect_of_no_reset`
- `ReturnGuard.terminalDefect_zero_or_exists_primitive_reset`
- `ReturnGuard.primitiveCyclotomicRadical_le_height_of_no_reset`

All are in
[`ReturnGuardTerminalGate.lean`](../MatrixMortality/ReturnGuardTerminalGate.lean).
