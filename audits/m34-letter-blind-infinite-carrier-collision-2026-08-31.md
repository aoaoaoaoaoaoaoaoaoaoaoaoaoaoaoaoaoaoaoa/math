# M₃(4) Letter-Blind Infinite-Carrier Collision Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `7c03987` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseInfiniteCollision.lean`](../MatrixMortality/TransverseInfiniteCollision.lean)

## Verdict

The literal generator used in `G3-O30`–`G3-O33` cannot recognize the `bcbc` paired zero language
for any rational source, terminal row, or column. It assigns the same matrix to both data labels,
so one certified terminal control and one certified nonterminal near-fork have identical matrix
products.

The infinite carrier orbit and universal terminal-coefficient section remain valid mathematical
components. A same-zero constructor must replace the letter-blind data map by two distinct maps.

## Opposite Source Semantics

`BranchingHistory` supplies the controls

```text
u = c t b c b t c b t,
v = b t c b c t c b t.
```

Here `t` denotes the paired phase toggle. Their exact source semantics for the width-three body
`bcbc` are

```text
pairedCoefficient(bcbc,u) = 0,
pairedCoefficient(bcbc,v) ≠ 0.
```

The first control decodes to the fixed terminal history `cbc,bcb`; the second decodes to the
same-length near-fork `bcb,ccb`. These facts were already kernel-checked independently of the
infinite-carrier construction.

## Product Collision

The explicit nonprojective generator is

```text
t ↦ T = diag(1,2,3),
b ↦ D_s,
c ↦ D_s.
```

The controls `u` and `v` have toggles in the same positions. Every other position is one of the
two data letters. After both letters map to `D_s`, their mapped word lists coincide term by term.
Lean unfolds the actual multiplication-ordered `wordProduct` and proves

```text
wordProduct(X_s,u) = wordProduct(X_s,v)
```

for every `s∈ℚ`.

Let `r` and `γ` be arbitrary rational row and column vectors. If their linear representation had
exactly the paired zeros of `bcbc`, source terminality of `u` would imply

```text
r X_u γ = 0.
```

Product equality gives `r X_v γ=0`, and the converse half of same-zero recognition would force
the paired coefficient of `v` to vanish. This contradicts the certified near-fork nonzero.

## Boundary Of The Cut

The theorem uses letter blindness, not rank, singularity, diagonalizability, or the specific
terminal row. It does not apply when the two data controls are distinct. In particular, it does
not prove any of the following:

1. that two distinct rank-two data maps cannot generate infinitely many carrier planes;
2. that the terminal scalar for such a pair still has at most two zero depths;
3. that a source-computed delayed target cannot coexist with letter separation;
4. that every nonprojective three-state architecture has a terminal/nonterminal collision;
5. that `M₃(4)` is decidable or undecidable.

The result also does not retract `G3-O30`–`G3-O33`. Their claims concern the carrier geometry and
terminal arithmetic of the displayed family, and remain correct. What fails is promotion of that
family, unchanged, to a complete paired recognizer.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The `bcbc` terminal and near-fork controls have opposite paired-zero semantics | inherited promotion | Lean theorem `BranchingHistory.bcbc_terminal_nearFork` |
| Their products coincide under the letter-blind infinite-carrier generator | promotion | Lean theorem `bcbcTerminal_wordProduct_eq_nearFork` |
| No row and column give that generator the `bcbc` zero set | promotion | Lean theorem `no_letterBlind_bcbc_sameZero` |
| The infinite carrier orbit itself is false | rejected | `G3-O30` remains formally valid |
| The universal coefficient section is false | rejected | `G3-O33` remains formally valid |
| Distinct singular data maps are impossible | rejected | the theorem assumes the maps are equal |
| The nonprojective architecture is closed | rejected | distinct data maps remain open |
| `M₃(4)` follows | rejected | no general lower bound or positive compiler is proved |

## Formal Validation

The formal owner compiles warning-free under the repository toolchain. Both publication-facing
declarations are listed in [`AxiomAudit.lean`](../AxiomAudit.lean), and their selected transitive
axiom outputs contain only the reviewed standard axioms. No `sorry`, `admit`, project axiom,
unsafe declaration, suppression, or proof aperture is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
KILLED: the literal G3-O30–O33 letter-blind generator as a complete paired recognizer.
CAUSE: one terminal and one nonterminal bcbc control have identical matrix products.
SURVIVOR: distinct source-computable rank-two data maps retaining infinite carriers and a
          terminal section, with a complete arbitrary-word converse.
```
