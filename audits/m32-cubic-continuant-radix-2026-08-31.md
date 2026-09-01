# M₃(2) Cubic Continuant Radix Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-O24` excludes bounded factorization of every upper-triangular recurrence word, but leaves
open a finite exact stabilizer nucleus: perhaps the upper-triangular words still represent only
finitely many projective transformations even though accepted factors have unbounded length.

The fixed false-wait family already refutes that nucleus. Two positive macro words act as a
common affine contraction with two distinct digits. Their products are a free binary positional
code inside the upper-triangular return language. Prefixing the known endpoint bridge by any
code word also gives a physical zero.

## Two Exact Macros

Let `Mₙ` be the false-wait return for the companion `X³+X²−1`. Direct multiplication gives,
up to the displayed nonzero scalars,

```text
M₅ = −6 [[4,274/12],[0,25]],

M₈M₁M₁₅M₈M₁M₈M₁₅M₂₁M₁₅
   = 1128443962982400000 [[4,149/12],[0,25]].             (1)
```

Both physical blocks use only positive waits. In affine coordinate `z=X/Y`, their normalized
actions are

```text
F₀(z)=(4/25)z+274/300,
F₁(z)=(4/25)z+149/300.                                  (2)
```

Thus every binary macro word is upper triangular. The two letters have the same contraction
ratio but different fixed points; the difference of their affine digits is `5/12`.

## Exact Radix Decoder

Put `d(0)=274`, `d(1)=149` and define

```text
κ(ε)=0,
κ(bw)=d(b)25^|w|+4κ(w).                                  (3)
```

Lean proves the complete normalized product formula

```text
F(w)₀₀=4^|w|,     F(w)₁₀=0,
F(w)₁₁=25^|w|,    F(w)₀₁=κ(w)/12.                       (4)
```

Equation (3) decodes from the head. Modulo four,

```text
κ(bw) ≡ d(b) (mod 4),     d(0)≡2,     d(1)≡1.           (5)
```

The residue determines `b`; subtracting its leading term and cancelling four recovers the
suffix recursively. Hence `κ` is injective at each fixed length. Projective equality of two
products first compares the diagonal ratios `(4/25)^|w|`, which determine the length, and then
(4)–(5) determine the word. Therefore

```text
F(u)=λF(v)  ⇒  u=v                                      (6)
```

for every rational `λ`. Independent nonzero physical scales in (1) preserve (6). In particular,
the fixed recurrence contains `2^n` projectively distinct upper-triangular continuants at every
binary macro depth `n`.

## Endpoint Consequence

The singular return is

```text
M₀=[[0,−79],[0,−90]].
```

For every upper-triangular `T`, direct multiplication gives `M₀T=T₁₁M₀`. The previously checked
bridge `P=M₁₂M₁₂M₈M₁₂M₁₂M₁₅M₈` satisfies `M₀PM₀=0`. Consequently every binary word gives

```text
M₀ F(w) P M₀=0.                                         (7)
```

Lean proves (7) using the physical macro expansion, not only normalized matrices. The positive
bridge `P` is invertible. Right cancellation therefore also proves that the bridge
transformations `F(w)P` remain projectively distinct.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the two physical macro products have the forms (1) | promotion | Lean checked |
| every encoded wait is positive | promotion | Lean checked |
| the normalized product has the positional form (4) | promotion | Lean checked |
| modulo four recursively decodes every equal-length word | promotion | Lean checked |
| the physical macro action is projectively injective | promotion | Lean checked |
| every binary macro word is upper triangular and extends the endpoint zero | promotion | Lean checked |
| the resulting endpoint bridge transformations remain projectively distinct | promotion | Lean-checked cancellation through the fixed invertible bridge |
| the fixed terminal continuant has a finite exact-product nucleus | rejected | (4)–(6) give exponentially many projective transformations |
| the current terminal ray itself ranges over infinitely many states at macro boundaries | rejected | every encoded macro product fixes the same ray at those boundaries |
| finite automata or finite abstract quotients are impossible | open | a finite recognizer need not store the exact projective product |
| the radix stack has a sound read or comparison operation | open | the present construction is write-only |
| the complete cubic continuant language or `M₃(2)` is decided | open | no arbitrary-word converse follows from the submonoid |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: every decision route requiring finitely many exact projective transformations in the fixed non-pure cubic terminal stabilizer
GAINED: an exact free binary write stack inside one fixed recurrence-digit continuant, with exponentially many projectively distinct endpoint-zero bridge transformations
NEXT DUAL: compose a recurrence-word read/compare operation with the radix stack, or prove that every possible reader leaks into a decidable affine quotient
```
