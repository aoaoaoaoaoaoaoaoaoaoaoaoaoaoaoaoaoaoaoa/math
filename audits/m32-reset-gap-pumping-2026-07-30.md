# M₃(2) Reset-Gap Pumping Audit

## Question

Does the moving Cramer-frame apparatus describe a genuine unbounded state, and can one fixed
legal wait macro support arbitrarily deep noncyclic returns to a rational checkpoint?

## Frame Closure

The evaluation frame

```text
F(j,H) = [j₀  1]
         [j₁  H]
```

has determinant `κ=Hj₀−j₁`. Lean verifies that the consecutive transition proposed for the
renormalized parameter jet is exactly `F⁻¹F′`. Products therefore telescope. The frame cocycle
is gauge.

Writing the fixed anchor evaluation as `A(j)=j₁+αj₀` gives

```text
κ = j₀(H+α)−A(j).
```

When `j₀` is a unit and `A(j)` has p-adic depth `d`, a defect deeper than `d` forces the state
onto the shell `vₚ(H+α)=d`. At a unit terminal payload, the defect is a unit. Thus deep `κ`
records reset-return precision; it is not an independent writable digit.

## Exact Similarity

For two residuals on the same legal wait branch `a`, direct subtraction of the Möbius formulas
gives

```text
vₚ(Sₐ(x)−Sₐ(y)) = vₚ(x−y)−sa.
```

Induction gives the corresponding law for any finite wait word and proves that a perturbation
deeper than the word weight follows the same schedule. A deep near-return therefore pumps
bounded repetitions of the same macro with exactly linear loss of depth.

## Rational Gap

For primitive integer representatives `(m,n)` and `(u,v)`, their projective determinant is
bounded by twice the product of their heights. If the represented unit rationals are distinct
and have p-adic separation `N`, the determinant is divisible by `pᴺ`; hence

```text
pᴺ ≤ 2H(m,n)H(u,v).
```

The existing canonical integral lift supplies the one-step height envelope

```text
H′ ≤ (|A|+|D|+|L|)H.
```

Combining these bounds with exact similarity proves that `r` legal repetitions of one wait
macro `w` from checkpoint `1` imply

```text
first return exact
```

or

```text
p^((r−1)s·sum(w)) ≤ 2(|A|+|D|+|L|)^length(w).
```

The strict reverse inequality forces an exact first-return cycle.

## Disposition

The parameter-lifting, anti-Hensel, anisotropic-lattice, renormalized-jet, rational-digit, and
moving-Cramer modules are strictly superseded. Their invariant content is the frame
coboundary and reset-shell localization above; their proposed state variable disappears.

The live problem is sequential. A decision proof should force a repeated macro inside every
sufficiently deep canonical return and apply the gap theorem. An undecidability proof must
construct moving checkpoints or a power-free nonperiodic wait schedule that evades every fixed
macro bound.

## Verification

The declarations are in
[`ReturnGuardFrame.lean`](../MatrixMortality/ReturnGuardFrame.lean) and
[`ReturnGuardGap.lean`](../MatrixMortality/ReturnGuardGap.lean). Both compile without warnings
under the repository's strict Lean gate. The full-project axiom snapshot owns their transitive
axiom boundary.
