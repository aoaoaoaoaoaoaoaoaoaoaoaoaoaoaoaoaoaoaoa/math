# M₃(2) Cubic Length-Nine Bridge Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S62` reduced every hit in the bounded length-eight bridge census to two length-seven cores.
The next question was whether those cores and five terminal-row aliases closed the positive
bridge language, or whether the next layer already contained genuinely new exact zeros.

## New Cores

An exact meet-in-the-middle search at length nine with every wait at most `30` returned `35`
bridge hits. Known boundary identities and the three new aliases below reduce `27` of them. The
eight remaining words are

```text
[22,3,5,15,4,15,6,8,2]
[21,1,8,7,1,7,1,8,7]
[7,16,15,7,7,7,1,8,7]
[8,7,1,1,17,15,1,8,7]
[22,22,8,22,19,15,8,1,8]
[10,12,15,8,12,1,15,11,8]
[3,15,1,21,17,1,15,22,8]
[7,16,15,4,1,15,21,22,8].
```

Lean indexes these words by `Fin 8`. For every index it checks the exact separator incidence

```text
rΠ(w)c=0
```

and derives the full matrix identity `M₀Π(w)M₀=0` from the rank-one factorization of `M₀`.

## New Aliases

For the terminal separator row `r=[0,1]`, Lean checks

```text
rΠ[4,1,8,7]=−180rΠ[13,15],
rΠ[7,16,15,1]=73440rΠ[13,15],
rΠ[15,8,16,1]=−(50400/13)rΠ[12,12].
```

Each scale is nonzero, so substituting the shorter right-hand boundary preserves zero incidence
against every suffix.

## Computational Boundary

The assertions that the bounded census contains exactly `35` hits, that `27` reduce through the
known aliases, and that the eight displayed words survive all checked shorter terminal-row
representatives through prefix length four are computational, not Lean theorems.

The same search exposed a strong provisional asymmetry. With waits at most `30`, the
terminal-row orbit has `89,567` projective collisions through depth four, whereas all `837,931`
separator-column words have distinct projective images. Exact column searches also found no
collision through depth four at waits at most `50`, depth three at waits at most `100`, or depth
two at waits at most `300`. These are bounded observations, not an injectivity theorem. Indeed,
global column injectivity fails already at length seven. Lean checks that the two core products
send the source to `[29617088832000000,0]ᵀ` and `[13080043192320000,0]ᵀ`; these are nonzero
vectors on the accepting ray and differ by the exact scalar `195925/86528`. The correct true
read-write block from `R32-O26` gives a second kind of collision at length `1175`, against the
empty word. Any decoder must stop at first acceptance and work modulo projective-neutral
insertion away from it.

## Adjudication

| Claim | Judgment |
| --- | --- |
| each displayed length-nine word has zero separator incidence | Lean checked |
| each displayed length-nine word gives a full zero bridge | Lean checked |
| all three displayed terminal-row aliases hold | Lean checked |
| the two length-seven cores collide projectively on the source orbit | Lean checked |
| the bounded search returned exactly `35` hits | exact computation, not formalized |
| exactly `27` bounded hits reduce through the checked aliases | exact computation, not formalized |
| the eight displayed words are globally irreducible | open |
| the raw separator-column orbit is projectively injective | rejected at equal depth seven |
| the nonaccepting source orbit is decodable modulo neutral insertion | open |
| a finite richer rewrite system exists | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
KILLED: closure of the positive bridge language on the two length-seven cores and S62 aliases
GAINED: eight exact new bridge cores and three exact terminal-row boundary rewrites
EXPOSED: a highly collisional left action and a source orbit whose first known merge is acceptance
NEXT: decode nonaccepting source prefixes modulo neutral insertion and classify first arrivals
      at the accepting ray
```
