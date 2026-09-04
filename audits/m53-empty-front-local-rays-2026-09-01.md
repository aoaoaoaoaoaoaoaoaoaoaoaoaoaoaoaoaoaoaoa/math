# M₅(3) empty-front local-ray audit

## Boundary

This audit concerns the empty-front arm of the swapped-ternary full-erasure-tail branch after
the two final singleton `D_c` transfers. It asks whether the exact local shells, primitive
three-adic normalization, or the `MM-S71` predecessor cylinder can eliminate that arm.

The result is negative. It constructs local backward projective rays only. It proves neither
reachability from the encoded entry nor a pole. No `M₅(3)` conclusion follows.

## Formal result

Let `β=offset+1≥3`, let `letters` be any word of length `β`, and let

```text
U = signedSwappedCode(tagEncode β letters ++ [true]),
P = 3^β(U+1)−1,
V = 3^β−1.
```

`EmptyFrontLocalRay` gives an exact body-independent pullback of `(P,V)` through
`D_b;D_c;D_c`. The three displayed forward scales have depths `β+1`, `1`, and `0`.
After the forced factors of three are removed, every displayed denominator and both coordinates
at the two earlier boundaries are three-adic units. The general primitive-reduction theorem
therefore cancels only three-adic-unit common factors, preserving these depths. The initial
`D_b` cylinder is

```text
3^(2β) · (−2H²R Q),
```

where `H=5·3^β−1`, `R=2−3^β`, and, with `s=3^(β−1)`,

```text
Q = 45s³U−75s²U+36sU−4U−36s²+18s−2.
```

The target suffix controls the exact gap depth. If `letters=c^β`, then

```text
v₃(2U+1)=β+1,       v₃(d₀−n₀)=2β+1.
```

Otherwise, if `letters=stem·b·c^t`, then

```text
v₃(2U+1)=t+2,       v₃(d₀−n₀)=β+t+2.
```

Thus all `2^β` empty-front targets satisfy the local width-square cylinder and the exact shell
pattern. This remains a local backward family only; no member is asserted reachable, and no
member is asserted to be a pole.

## Height diagnostics

Exact integer search rejects two natural globalizations. At `β=6`, lawful body `bcccc`, empty
target `c^6`, and initial `w=D_b`, pulling backward once through `(R_c,D_b)` and then through
`D_c` changes the primitive pair

```text
(882905085984278746564882420678,
 882892906691284588711730858269)
```

to

```text
(2951448668917586413728623781,
 706025201151410847057851585687).
```

The Farey height `max(|n|,|d|,|d−n|)` contracts by approximately `0.7996615`; the ordinary
maximum-coordinate height also contracts. This is computational evidence, not a formal theorem.
It rejects a universal one-step norm argument. The initial shell does lie in a robust expanding
multicone: exhaustive width-six search over all minimal bodies, all 64 empty targets, and every
shell-compatible preceding block of role length at most four found no first-level Farey-height
contraction across 29,419,520 edges. One additional lawful inverse block exits that multicone.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterEmptyFrontRay.lean`](../MatrixMortality/SwappedSetterEmptyFrontRay.lean).

The publication-facing entry points are `exists_emptyFrontLocalRay`,
`emptyTarget_gapCore_padicValInt_cases`, and
`emptyTarget_antecedentGap_padicValInt_cases`. The module, umbrella, namespace linter, and full
axiom audit pass without warnings. Lean LSP reports zero diagnostics. The three entry points have
the reviewed axiom set `[propext, Classical.choice, Quot.sound]`; every public theorem is listed
in `AxiomAudit.lean`. The aperture scan is empty.

## Consequence

Local shell, residue, and fixed-cylinder arguments cannot close the empty-front arm. The next
proof must use forward entry reachability, a history-sensitive multicone or multi-step weight,
or target-prefix ancestry before the three-block window. The arbitrary-target-suffix obligation
remains independent.
