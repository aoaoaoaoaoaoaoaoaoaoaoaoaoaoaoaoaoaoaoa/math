# M₃(2) Cubic Source-Stabilizer Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S71` exhibits nonzero scalar-identity insertions inside the selected source zero. A proposed
repair would quotient only those projective-neutral words. This audit tests whether the source
fibre contains a nonscalar positive stabilizer.

## Certificate

Three available positive terminal translations obey

```text
25(2839/108) + 5(-189665/144) + 1221(31457/6480) = -11/10.
```

Appending their physical repetitions to the false radix writer realizes

```text
H = [[4/25,137/150],[0,1]] [[1,-11/10],[0,1]]
  = [[4/25,553/750],[0,1]].
```

For the original separator source `c=(-79,-90)ᵀ`, exact multiplication gives `Hc=c`. The two
diagonal entries `4/25` and `1` prove that `H` is not projectively scalar.

The positive spelling of `H` has length `29,004`. Appended after the length-eight selected source
word `E₀₀`, it gives a length-`29,012` word satisfying

```text
Π(E₀₀H)c = σΠ(E₀₀)c,       σ≠0.
```

The selected source product is a unit because all eight waits are positive. Left cancellation
therefore proves that `Π(E₀₀H)` and `Π(E₀₀)` are not projectively equal.

## Adjudication

| Claim | Judgment |
| --- | --- |
| terminal translation sum `-11/10` | Lean checked |
| nonzero physical realization of `H` | Lean checked |
| exact source fixation `Hc=c` | Lean checked |
| `H` is not projectively scalar | Lean checked |
| positivity and lengths `29,004`, `29,012` | Lean checked |
| selected-source ray collision | Lean checked |
| projective matrix separation | Lean checked |
| full source-fibre classification | open |
| arbitrary raw-word converse | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: an explicit positive non-scalar stabilizer of the original separator source
KILLED: scalar-identity insertion as the complete quotient obstruction
EXPOSED: a double-coset/source-fibre normal-form problem
NEXT: classify left target and right source stabilizers, then attack raw-word recognition
```
