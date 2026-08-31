# Separated Two-C Residue-Five Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

For every `k≥0`, the coupled width-three tag system with

```text
q = bb c b^(9k+5) c b^(9k+5),
b ↦ b,
c ↦ qb
```

halts from `q.drop 2 · b`. The proof is uniform and kernel-checked. It reduces the exact
two-active-`c` dynamics to an injective partial map on a finite defect interval and proves that
the coupled initial point must reach a draining residue.

## Exact Macro

Put `A=3k+2`, so the separation is `n=3A-1`. At an active-pair boundary use the canonical
queue

```text
P(A,r) = c b^(3A-1) c bʳ.
```

Processing its two active `c` heads gives an exact intermediate queue. Its continuation splits
according to `r mod 3`:

| Tail | Exact consequence |
| --- | --- |
| `r=3g` | equivalent at every future width-three head to `P(A,10A+g+2)` |
| `r=3g+2` | reaches `P(A,16k+g+12)` |
| `r=3g+1` | reaches a queue with `b` at every index divisible by three and drains |

The first row contains two `c` letters that never occur at a deletion head. Lean proves a
general equal-length head-equivalence bisimulation: queues agreeing at every index divisible by
three take equivalent next steps, and halting transports in both directions. Replacing those
two inert letters by `b` therefore establishes the stated canonical successor without deleting
behavior from the proof.

## Cantor Defect

Define

```text
E = 15A+3-r,
H = 7A+2.
```

For `0<E<H`, the three tail cases become

```text
E mod 3 = 0:  E' = E/3,
E mod 3 = 1:  E' = (E+2H)/3,
E mod 3 = 2:  drain.
```

Because `H≡1 (mod 3)`, both live branches are integral, remain strictly inside `(0,H)`, and
send their inputs into disjoint outer thirds. They are jointly injective on live defects.

The coupled queue first uses the `r=3A` branch and enters the defect system at
`E₀=4A+1`. It satisfies

```text
0 < E₀ < H,
H < 3E₀ < 2H,
```

so it lies in the open middle third. Suppose no iterate reached residue two. All iterates would
then remain in the finite interval `(0,H)`, hence two would coincide. Injectivity cancels their
common prefix and puts `E₀` on a nontrivial cycle. Its predecessor maps to `E₀`, forcing `E₀`
into an outer third, contrary to the displayed inequalities. A residue-two iterate therefore
exists, and induction over its first occurrence pulls the draining certificate back through the
exact tag macros to the coupled source.

## Checked Boundary

[`MatrixMortality/SeparatedTwoCCantor.lean`](../MatrixMortality/SeparatedTwoCCantor.lean) proves
the head-equivalence bisimulation, each exact queue macro, injectivity and finite death for the
Cantor-defect map, and
`SeparatedTwoCResidue.fiveResidue_tagHaltsFrom` for every `k`.

Together with `MM-S25` and `MM-S30`, this reduces the diagonal to `n≡2 (mod 9)`; `MM-S41`
later reduces that class to `n≡11 (mod 27)`, and `MM-S43` further reduces it to
`n≡38,65 (mod 81)`. The theorem does not decide unequal outer runs, arbitrary separated
two-`c` bodies, or the existence of a universal deletion-width-three source family.
