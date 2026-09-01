# M₃(2) Cubic Endpoint-Chart Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The fixed cubic family was reduced to a scalar bridge, but its left and right actions have very
different collision structures. A lawful decision attack needs a coordinate system in which the
source, accepting locus, invertibility, and collision obstruction are all exact.

## Chart

Lean verifies

```text
B=[[-79,1],[-90,0]],
B⁻¹=[[0,−1/90],[1,−79/90]],
B⁻¹B=BB⁻¹=I.
```

The separator source is `Be₀=[−79,−90]ᵀ`, and its terminal row obeys `rB=−90e₀ᵀ`. For cubic
state `(a,b,c)`, direct conjugation gives

```text
B⁻¹M(a,b,c)B=
[[-79a−30b−90c, a],
 [−3424a−2376b, 16a+24b]].
```

The proof is symbolic over the state entries, not a finite wait census.

## Word Reduction

Lean proves wordwise conjugacy and determinant transport:

```text
Π(T,w)=B⁻¹Π(M,w)B,
det Π(T,w)=det Π(M,w).
```

It then evaluates the separator incidence exactly:

```text
rΠ(M,w)c=−90·Π(T,w)₀₀.
```

Every relabelled positive endpoint generator is a unit, hence so is every positive word product.
Therefore its first column cannot vanish. The upper-left entry is zero exactly when that column
is a nonzero multiple of `e₁`. Combining this fact with the arbitrary-word punctuation theorem
from `R32-S61` yields

```text
IsMortal(M) ↔ ∃ positive endpoint word w, ∃λ≠0, Π(T,w)e₀=λe₁.
```

## Collision Boundary

The endpoint chart does not make the source orbit free. Lean checks for the two distinct
length-seven bridge cores `A,B`:

```text
Π(T,A)e₀=29617088832000000e₁,
Π(T,B)e₀=13080043192320000e₁,
Π(T,A)e₀=(195925/86528)Π(T,B)e₀.
```

Thus projective injectivity fails at equal length on the accepting fibre. The neutral-word
obstruction `R32-O26` also forbids raw injectivity away from any syntax quotient. A lawful next
step must classify ray-specific stabilizer loops as well as accepting arrivals; this audit does
not assume that nonaccepting prefixes decode uniquely.

## Adjudication

| Claim | Judgment |
| --- | --- |
| `B` and `B⁻¹` are exact inverses | Lean checked |
| the displayed state formula holds | Lean checked |
| conjugacy and determinant transport hold for every word | Lean checked |
| the bridge scalar is `−90` times the upper-left endpoint entry | Lean checked |
| every positive endpoint word product is a unit | Lean checked |
| scalar-bridge zero is equivalent to nonzero `e₁`-ray reachability | Lean checked |
| mortality of the fixed family is equivalent to positive `e₁`-ray reachability | Lean checked |
| the two length-seven words collide projectively on the accepting fibre | Lean checked |
| nonaccepting prefixes have a unique decoder | not claimed |
| all source-ray stabilizer loops are classified | open |
| all accepting-ray arrivals are classified | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: exact separator-adapted conjugacy and a complete accepting-ray reachability reduction
KILLED: raw or equal-length projective source freeness as the prospective decision theorem
EXPOSED: source-ray stabilizers and accepting arrivals as the exact projective language
NEXT: classify stabilizer loops and every entry into the e₁ ray before positing a decoder
```
