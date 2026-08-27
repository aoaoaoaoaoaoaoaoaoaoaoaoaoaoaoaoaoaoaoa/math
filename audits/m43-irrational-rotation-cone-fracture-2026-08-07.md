# M₄(3) irrational-rotation cone-fracture audit

**Date:** 7 August 2026

**Status:** finite Archimedean cone certificates are impossible; `M₄(3)` remains open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** adjudicate the proposed exterior cone attack and replace it only if its failure
changes the master-level strategy

## Verdict

The returned obstruction is correct. One legal regular atom already defeats the complete finite
cone program. For every `β≥1`, repeated application of `G=Q(b,4)` produces a dominant irrational
rotation in the real projective exterior plane. Its orbit changes the sign of the bridge
determinant infinitely often and accumulates on the singular wall, although an exact `3`-adic
invariant proves that it never reaches that wall.

This excludes the proposed finite componentwise proper-cone systems and every finite strict
Markov certificate whose recurrent regions remain separated from `u=0`. The conclusion is not a
safe-return theorem: arithmetic, infinite, or non-strict invariants remain possible, as do exact
safe returns and malformed zeros.

Formalization strengthened the arithmetic statement. If `uₙ=3ⁿaₙ`, then every `aₙ` is an integer
congruent to `1` modulo three. This proves `v₃(uₙ)=n` without a cancellation argument at each
inductive step.

No Lean declaration was added. A recurrence for one cyclic safe language has no current Lean
consumer, while formalizing the surrounding real spectral, Galois, projective, and proper-cone
argument would create a large theory used only to retire an attack. The exact reconstruction and
proof audit suffice for an audited obstruction; the finite-cone route itself is removed from the
frontier.

## Provenance And Legality

The return was made against branch `m43-cube-root-incidence` at
`d64720f1850c3ba8523b7138bf7fa022fb2e9917`. The extracted transient artifacts have digests

```text
transcript  3766ded09584d793a579bc036953db570f49b08183083ae1d6e0c38df45a4405
report      f579507cf0ee381fb4e66e61a453c9190b4b8c24b637ac2f5a3b3eec9535c3a9
```

The repository defines

```text
(letter,j,true) ↦ Q(letter,3j+1).
```

Thus `(b,1,true)` is exactly `Q(b,4)`. It is a legal safe label, and its determinant is
`216·3^β`, so it is regular. Arbitrary lists of safe labels are admitted; every power `Gⁿ` is a
genuine safe word rather than a formal matrix orbit outside the grammar.

An independent SymPy reconstruction starts from `normalRoot`, `bFlank`, and `injection`, derives
`Q(b,4)`, and checks the exterior conjugacy, characteristic polynomial, discriminant, recurrence,
initial terms, and sampled exact orbits. The passing script
`/tmp/m43_rotation_check.py` has SHA-256
`646b6705a7c8d0eefc77b09f474853e96318249687c4bed7ef59c88fcd866ff6`.

## Exact Cyclic Theorem

Put `r=3^β` with `β≥1`. In the checked triangle coordinates, the empty bridge state and
singular wall are

```text
x₀=(0,22,9)ᵀ,          u=0.
```

Direct reconstruction from the atom definition gives

```text
Aᵣ = T_b1(1)
   = [[12−144r, −24, 12−144r],
      [315r,       0,      216r],
      [(297/2)r,   0,      108r]].
```

More precisely, for the raw exterior state `z(W)=adj(W)ᵀ(22,−31,−36)ᵀ`, the change of basis

```text
P = [[−1,−1, 1/4],
     [ 1, 0,   0],
     [ 0, 0,−1/4]]
```

satisfies `Pz(I)=x₀` and

```text
P adj(Q(b,4))ᵀ P⁻¹ = Aᵣ.
```

The first row of `P` is `−(1/4)(4,4,−1)`, the checked bridge wall covector. Hence left
multiplication by the atom acts on the suffix state exactly as `x↦Aᵣx`; no false multiplicative
law for `K(UV)` is used.

For `xₙ=Aᵣⁿx₀=(uₙ,vₙ,wₙ)ᵀ`, the characteristic polynomial is

```text
pᵣ(X)=X³+(36r−12)X²+(7074r+5832r²)X−46656r².
```

Cayley–Hamilton yields

```text
uₙ₊₃=−(36r−12)uₙ₊₂−(7074r+5832r²)uₙ₊₁+46656r²uₙ,
```

with

```text
u₁=−12(108r+35),
u₂=144(324r²+69r−35),
u₃=216(27216r³+54720r²+15147r−280).
```

Set `aₙ=uₙ/3ⁿ`. The three displayed values are integers congruent to `1` modulo three. Dividing
the recurrence by `3ⁿ⁺³` gives the integral recurrence

```text
aₙ₊₃=(4−12r)aₙ₊₂−(786r+648r²)aₙ₊₁+1728r²aₙ.
```

Because `3∣r`, its coefficients are respectively `1,0,0` modulo three. Induction gives

```text
aₙ ≡ 1 (mod 3),       v₃(uₙ)=n       for every n≥1.
```

Using the checked bridge identity `det K(Gⁿ)=(9r/2)uₙ`, every nonempty cyclic bridge is
invertible and

```text
v₃(det K(Gⁿ))=β+n+2.
```

## Irrational Dominant Plane

The discriminant factors as

```text
Disc(pᵣ)=−209952r²F(r),
F(r)=3569184r⁴+14180832r³+17747946r²+6540237r−32786.
```

For `r≥3`, `F(r)>0`, so `pᵣ` has one real root and a nonreal conjugate pair. Moreover,

```text
pᵣ(0)<0,             pᵣ(8)=16(3681r−16)>0,
```

and the unique real root `α` lies in `(0,8)`. The cubic is irreducible over `ℚ`: a rational root
would be an integer in `{1,…,7}`; roots prime to three are excluded modulo three, while direct
evaluation at `3` and `6` gives nonzero values. If `λ,λ̄` are the complex roots, then

```text
α|λ|²=det Aᵣ=46656r²>α³,
```

so `|λ|>α`.

Irreducibility and the nonsquare discriminant give an `S₃` splitting field. Its only proper
nontrivial Galois subfield is `ℚ(√Disc(pᵣ))`. Since

```text
209952=2⁵3⁸,
```

and both `r` and `F(r)` are odd, the square class has `2`-adic valuation five. The quadratic
subfield is therefore neither `ℚ(i)` nor `ℚ(√−3)`. An `S₃` splitting field with that quadratic
subfield contains no roots of unity other than `±1`. The ratio `λ/λ̄` is neither value: `1` would
make `λ` real, while `−1` would force `α=12−36r<0`. Thus `λ/λ̄` is not a root of unity.

Let `Π` be the real invariant plane of `λ,λ̄`. The projection of `x₀` to `Π` is nonzero because
`Aᵣx₀` is not proportional to `x₀`. The functional `u` is nonzero on `Π`, since otherwise
`Π={u=0}` would be invariant, whereas

```text
Aᵣ(0,1,0)ᵀ=(−24,0,0)ᵀ.
```

The dominant action on `Π` is similar to an irrational rotation followed by scaling. Hence

```text
ω([xₙ])=P(Π).
```

The plane `Π` meets `{u=0}` in a line. The normalized orbit therefore approaches the wall along
a subsequence, and the nonzero values `uₙ` take each sign infinitely often.

## Certificate Obstruction

Suppose finitely many proper closed convex cones satisfy componentwise transitions

```text
AᵣC_q ⊆ ε_q C_σ(q),       ε_q∈{−1,1}.
```

A cycle of `σ`, followed twice if necessary, gives `Aᵣ²ᵐC⊆C` for some proper cone `C` and
`m≥1`. A matrix preserving a proper cone has a nonnegative real eigenvalue equal to its spectral
radius; this is the Krein–Rutman consequence recorded as Fact 1 in
[Protasov's local source record](../references/protasov-2026-perron-matrix-semigroups-v2.md).
But the dominant eigenvalues of `Aᵣ²ᵐ` are `λ²ᵐ,λ̄²ᵐ`. They are nonreal, because reality would
make `(λ/λ̄)²ᵐ=1`, and they strictly dominate `α²ᵐ`. This is impossible.

The wall-accumulation statement separately excludes every finite closed projective cover of this
orbit whose components avoid the wall: a finite union is compact and has positive distance from
the wall. For open Markov regions with strict inclusions, the finitely many image closures give
the same compact tail cover. Convexity is irrelevant to this second obstruction.

Consequently the proposed rational-polyhedral/componentwise cone architecture and every finite
strict wall-separated Markov multicone fail even for one fixed admissible instance and one legal
atom. Parameter-uniform base/direction inequalities cannot repair a class already contradicted
by `T_b1(1)`.

This does **not** exclude an infinite cone family, a non-strict invariant whose closure meets the
wall, a nonconvex arithmetic partition, a hybrid real/`3`-adic certificate, or a finite structure
that carries exact arithmetic rather than a wall-separation margin.

## Disposition

| Claim | Disposition |
| --- | --- |
| `Q(b,4)` is a legal regular safe atom and its powers use the stated transition | independently reconstructed |
| `v₃(uₙ)=n` | strengthened to `uₙ/3ⁿ∈1+3ℤ` and audited |
| Dominant irrational projective rotation and wall accumulation | audited |
| No finite componentwise proper-cone system | audited |
| No finite strict wall-separated Markov certificate | audited with the certificate class stated explicitly |
| No arbitrary finite nonconvex or arithmetic certificate | rejected as overbroad; not proved |
| Full safe return, arbitrary defect isolation, or `M₄(3)` | open |

## Exact Wound

```text
MASTER VERDICT: still open
REMOVED: every finite Archimedean cone or strict wall-separated multicone proof of complete
         safe return
REMAINS: exact safe return for arbitrary residue-{0,1} words; then the alternating one-defect
         phases and interactions among multiple residue-two defects; independently, the
         missing undecidable binary deterministic two-state scalar source
DISTANCE: build an arithmetic/infinite/hybrid safe-return invariant that survives the hostile
          Q(b,4)^n cycle, or find an exact safe return/malformed zero and retire the blade;
          after safe return, consume it immediately in the complete all-word converse
```

No durable source was newly acquired. The external transcript, report, symbolic scripts, and
next prompt remain transient under `/tmp`.
