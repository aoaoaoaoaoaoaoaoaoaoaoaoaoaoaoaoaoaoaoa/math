# Audit of the `GPCP(4)` and `M₃(5)` Results

## Verdict

**The former Rote conditionality is closed.** The proof no longer relies on Rote's long unary
terminal block. A universal block-forcing and queue-history argument proves directly that
Neary's four ordinary pairs reach the fixed-right-boundary equation exactly when the restricted
tag system halts. A fresh-marker fifth pair then supplies a corrected binary five-pair PCP
family with the required primitive-terminal property.

Combining this checked source theorem with Neary's peer-reviewed Lemma 9 proves, on ordinary
mathematical standards:

```text
GPCP(4) is undecidable;
M₃(5) is undecidable.
```

The source theorem, corrected PCP, complete arbitrary-product matrix reduction, and structured
matrix promises are machine-checked. The remaining formalization boundary is Neary's Table 2
universality compiler itself, not a gap in the new proof. Thus “the novel reduction is formally
verified” is accurate; “the entire undecidability theorem has been derived in Lean from a
formal Turing-machine halting theorem” is not yet accurate.

| Component | Adjudication |
| --- | --- |
| Exact match equation for the four ordinary tiles | Pass; formally verified for arbitrary label words |
| Exclusion of malformed prefix-comparable paths | Pass; pulse parser plus history soundness |
| Tag halting ⇒ terminal match | Pass; invariant and formally verified |
| Fresh-marker binary five-pair PCP | Pass; solvability and primitive terminality formally verified |
| Four-generator GPCP bridge | Pass; formally verified |
| Exact five integer matrices | Pass; arbitrary-product converse formally verified |
| Four nonsingular triangular plus one nonzero rank-one matrix | Pass; formally verified |
| Neary restricted-tag source undecidability | Published external theorem; exact parameter seam audited |
| Undecidability-antichain arithmetic | Pass against CHHN definitions and theorem parameters |
| Accepted or independent prior proof | None found; priority remains intrinsically noncertifiable |

## What Was Wrong With the Previous Route

Neary's STACS 2015 Theorem 11 uses the terminal pair

```text
(10^β 1111, 1111).
```

Its converse asserts that adjacent encoded `c` symbols cannot occur. That assertion is false.
Rote replaces the four ones by a much longer unary block and states the primitive-terminal
property needed by later work. His density invariant controls reachable tag datawords and the
intended deletion phase, but the printed proof does not exhaust wrong choices that remain
prefix-comparable.

One omitted branch, beginning at the genuine halt residual `↓10^β`, is:

```text
↓10^β  --R_b-->  ↓10  --D_b-->  ↑0^(β−2)1
                     --D_c^(β−2)--> ↑1^(β−1).
```

This is not a counterexample to Rote's theorem, but it refutes any proof that assumes the lower
side always remains longer or that a wrong choice immediately mismatches. The old manuscript's
Appendix A made precisely that unjustified exhaustiveness leap and has been deleted.

## The New Source Proof

Let `β≥3`, let `q∈{b,c}*`, and consider the tag system

```text
b ↦ b
c ↦ q b
```

with deletion width `β` and initial queue `drop_(β−1)(q) b`. Encode

```text
H(b)=10^β1,  H(c)=1,  M=10^β.
```

The four ordinary pairs are:

```text
R_c = (1,       1 H(q) 10)
R_b = (10^β 1,  110)
D_c = (1,       0)
D_b = (10^β 1,  0).
```

### Exact block forcing

In every upper concatenation followed by `M`, every positive zero run has length exactly `β`
and the word ends after such a run. An exact finite-state scan of the equal lower concatenation
shows:

- the first label must be a rule label;
- a rule lower word leaves a zero-run count of one;
- exactly `β−1` erase labels must follow;
- another rule is possible only after the count reaches `β`;
- an erase at count `β` is impossible.

Thus every solution word, including every malformed candidate, is a concatenation of blocks

```text
R_(a₀) D_(a₁) ... D_(a_{β−1}).
```

The upper labels of a block are a width-`β` stroke of deleted tag symbols.

### Queue-history soundness

After appending one final `1`, the terminal marker becomes `H(b)`. Injectivity of `H` converts
the word equality into

```text
consumed(history) · b = initial · produced(history).
```

The first block is forced to be the initialization block
`c · take_(β−1)(q)`; cancellation leaves the displayed equation for the remaining history.

A generic lemma proves that any such equation with a final word shorter than `β` yields a lawful
tag run. Inductively, either the current queue is already short, or its first `β` symbols and the
next stroke are equal because both are prefixes of the same global word. One lawful step and
left cancellation reduce the history. Crucially, the induction stops at the first short queue;
it never needs to interpret Pro's post-halt wandering branch.

### Converse

A lawful finite tag run supplies its deleted width-`β` strokes. Every reachable queue ends in
`b`. If `β−1` divides `|q|`, queue length is invariantly `1 mod (β−1)`. Therefore a reachable
queue shorter than `β` is exactly the singleton `b`, and the history closes the terminal
equation.

The resulting theorem is:

```text
∃w, U(w) 10^β = V(w)
  ↔ the restricted tag system halts.
```

No residual-language classification, long unary guard, or primitive-solution hypothesis is
used.

## Embedding Neary's Undecidable Family

This identification was checked directly against Lemma 9 and the proof of Theorem 11 in the
local Neary PDF.

Neary has `β=10p`, rule `b↦b`, whole `c`-appendant `q b` of length `βs`, and initial queue
`q_{β−1}q_β...b`, exactly `drop_(β−1)(q)b`. For cyclic-program length `p`, input length
`n`, and maximum cyclic appendant length `r`, put

```text
B = max(11(n+p)+β−2, 11p, 11r, 1)
x = ceil((B−1)/(β−1))
s = x(β−1)+1.
```

Then `s≥B` and `s≡1 mod (β−1)`. The variable exponents in Neary's Table 2 are
`s−11(n+p)−β+2`, `s−11p+1`, `s−11p`, `s−11v+1`, `s−11v`, and `s−1`, where `v≤r`;
all are nonnegative. Thus this is a computable choice within Neary's stated freedom to take
`s` above a construction-dependent constant, and it preserves every track length and shift
residue used by the simulation. In particular, it has the required form

```text
s = x(β−1)+1.
```

Hence

```text
|q| = βs−1 = (xβ+1)(β−1),
```

which is at least `β−1` and divisible by `β−1`. These are precisely the hypotheses of the new
source theorem. Lean's `NearyArithmeticEnvelope` records only these arithmetic conditions; it
is deliberately broader than the set of actual Table 2 compiler outputs.

The external theorem we retain is only Neary's Lemma 9: halting of this restricted family is
undecidable. We do not import the defective converse of his five-pair PCP Theorem 11.

## Corrected Five-Pair PCP

Introduce a fresh symbol `#`, lift the four ordinary pairs, and add `(10^β#, #)`. Encode the
three symbols by the fixed-length binary code

```text
0 ↦ 00,  1 ↦ 01,  # ↦ 11.
```

Every ordinary upper image ends in `1`, while every ordinary lower image ends in `0`; an
ordinary-only word cannot solve PCP. At the first terminal occurrence, prefix comparability of
`x#` and `y#` forces `x=y`, so the prefix already closes a solution. A primitive solution can
have no nonempty suffix and therefore contains tile five exactly once and last.

This gives a corrected five-pair theorem independently of Rote's quantitative repair and
supplies the abstract primitive-terminal interface used by the older formal modules.

## GPCP and Matrix Consequences

The terminal equation is directly a four-generator GPCP instance with empty left boundaries,
upper right boundary `10^β`, and empty lower right boundary. Its empty word cannot solve the
equation, so this is also the nonempty-witness `GPCP⁺(4)` form required by CHHN.

For the matrices, recode `0,1` as ternary digits `1,2` and use the standard morphism `Ψ`. For
the four ordinary pairs let `Xᵢ=Ψ(Uᵢ,Vᵢ)`. Put

```text
X★ = Ψ(10^β, ε)
A★ = X★ e₃ e₁ᵀ.
```

The five generators are `X₁,...,X₄,A★`. Products without `A★` are nonsingular. Every product
with separators factors as

```text
(P₀c) · ∏(e₁ᵀPⱼc) · (e₁ᵀPₜ),    c=X★e₃.
```

The exterior vectors are nonzero. Thus a product is zero exactly when an internal scalar is
zero, and that scalar is zero exactly when the corresponding ordinary label block satisfies
`U(w)10^β=V(w)`. This covers all product shapes, including adjacent separators and empty
blocks.

The direct compiler is prior technique, not the novelty claim. HHH07 contains forced-endpoint
rank-one absorption, and CHHN's `GPCP→Z→M` construction specializes to the same outer product.

## Undecidability-Antichain Consequences

CHHN's Theorem 4 trade `M_d(hk+1) ≤ₘ M_{kd}(h+1)` gives:

| Parameters | Consequence | Newly filled by padding |
| --- | --- | --- |
| `h=2, k=2` | `M₆(3)` | `(6,3), (7,3), (8,3)` |
| `h=1, k=4` | `M₁₂(2)` | `(12,2), (13,2), (14,2)` |

Together with `M₅(4)`, the minimal known mortality undecidability antichain is:

```text
M₃(5), M₅(4), M₆(3), M₁₂(2).
```

Using CHHN's actual definition of `Z_d(k)` as scalar reachability `LYC=0`, the proof of their
Theorem 1, Theorems 3, 6, and 7, and Propositions 3 and 4 give the parallel minimal known
undecidability antichains:

```text
Z₃(4), Z₅(3), Z₇(2)
R₃(5), R₄(4), R₆(3), R₈(2).
```

## Formal Verification

The exact theorem map and trust model are in [FORMALIZATION.md](FORMALIZATION.md) and
[FOUNDATIONS.md](FOUNDATIONS.md). The strongest publication-facing declarations are:

```text
terminal_match_iff_tagHaltsFrom
nearyPCP_solvable_iff_tagHaltsFrom
nearyPCP_primitive_terminal
nearyGPCP_solvable_iff_tagHaltsFrom
nearyGPCPPlus_solvable_iff_tagHaltsFrom
nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom
NearyArithmeticEnvelope.mortality_iff_halts
```

The project builds with no `sorry`, `admit`, custom axiom, unsafe theorem, or `native_decide`.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

The one remaining external mathematical theorem is Neary's restricted-tag universality. A
fully closed proof assistant artifact would formalize his cyclic-tag compiler and a many-one
reduction from a machine-halting predicate. It would be dishonest to hide this seam behind a
new Lean axiom.

## Novelty Posture

The detailed search log remains in [NOVELTY.md](NOVELTY.md). The safe claims are:

- Neary13 prevents “first public statement” or “first unconditional claim” of `M₃(5)`.
- Its four-pair PCP premise was not retained in the refereed successor, but no formal
  withdrawal, published diagnosis, or independently verified counterexample was found.
- HHH07 and CHHN prevent “new rank-one absorption technique.”
- No valid earlier proof of `GPCP(4)` or `M₃(5)` was found.
- The new block-forcing source proof and fresh-marker repair are not present in the audited
  literature.

Use “a proof of the previously unestablished case” or, when priority matters, “to our
knowledge, the first valid proof,” until Neary, Rote, Nicolas, and a CHHN/HHH author have
reviewed the manuscript and the counting convention.

## Remaining Submission Obligations

1. Obtain independent expert review of the source theorem, especially Equations (1)–(4), the
   compiler-output embedding, and the congruent padding lemma.
2. Ask the source and matrix authors about prior circulation or alternate terminology.
3. Preserve the present Lean source, toolchain pin, dependency lock, axiom log, and artifact
   hashes in every future published snapshot. The current repository satisfies this obligation.
4. If claiming full formal verification of undecidability, first formalize Neary's Lemma 9
   compiler; otherwise state the current boundary exactly.

The revised eight-page manuscript is [paper/main.pdf](paper/main.pdf).
