# M₃(2) Cubic Bridge-Alias Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S61` reduces the complete fixed family to a scalar language of positive bridges. Exact
search found multiple bounded bridge zeros. Before treating them as distinct phenomena, their
terminal-row actions must be quotiented by every exact projective alias.

## Boundary Identities

For the separator row `r=[0,1]`, Lean checks

```text
rM₁=60r,
rM₅=−150r,
rM₁₄=510r,
rM₄M₆=−7rM₁₃,
rM₃M₈M₁=(30/13)rM₁₂M₁₂.
```

All five scales are nonzero. Prefixing a bridge by any of the first three letters does not
change its zero incidence. The last two equations replace a longer boundary word by a shorter
one without changing that incidence.

## Eight-Hit Reduction

The two length-seven cores are

```text
A=[13,15,29,11,13,7,8],
B=[12,12,8,12,12,15,8].
```

An exact length-eight search with waits at most `30` returned these hits and reductions:

| Hit | Core | Scale |
| --- | --- | ---: |
| `[1,13,15,29,11,13,7,8]` | `A` | `60` |
| `[4,6,15,29,11,13,7,8]` | `A` | `−7` |
| `[5,13,15,29,11,13,7,8]` | `A` | `−150` |
| `[14,13,15,29,11,13,7,8]` | `A` | `510` |
| `[1,12,12,8,12,12,15,8]` | `B` | `60` |
| `[3,8,1,8,12,12,15,8]` | `B` | `30/13` |
| `[5,12,12,8,12,12,15,8]` | `B` | `−150` |
| `[14,12,12,8,12,12,15,8]` | `B` | `510` |

Lean defines the hit, core-index, and scale maps on `Fin 8`, then proves the corresponding row
identity for every index. It proves both core scalar incidences zero and derives all eight full
matrix bridge zeros using rank-one outer-product algebra.

## Computational Boundary

The claim that these are all hits in the stated length-eight box comes from exhaustive exact
computation and is not a Lean theorem. A larger exact length-seven census with the first six waits
at most `200` and the last wait at most `50` returned only `A` and `B`; a two-prime modular
meet-in-the-middle filter had no false candidates in that range. These are search observations,
not a global classification.

## Adjudication

| Claim | Judgment |
| --- | --- |
| the three triangular-prefix identities hold | Lean checked |
| the two boundary rewrite identities hold | Lean checked |
| each indexed length-eight word reduces to its displayed core and scale | Lean checked |
| each indexed length-eight word is an exact bridge zero | Lean checked |
| the bounded search returned no other hit | exact computation, not formalized |
| every positive bridge reduces to `A` or `B` | open |
| the boundary rewrite system terminates and is confluent | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: all eight bounded length-eight hits as independent bridge cores
GAINED: five exact terminal-row aliases and two surviving length-seven cores
EXPOSED: rewrite completion of the positive scalar bridge language as a concrete decision seam
NEXT: orient the aliases, seek a decreasing normal-form measure, and hunt the first third core
```
