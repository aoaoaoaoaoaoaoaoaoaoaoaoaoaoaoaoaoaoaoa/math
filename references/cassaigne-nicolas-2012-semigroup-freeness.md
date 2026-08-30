# Cassaigne and Nicolas (2012): On the decidability of semigroup freeness

**Citation.** Julien Cassaigne and François Nicolas, “On the Decidability of Semigroup
Freeness,” *RAIRO. Theoretical Informatics and Applications* 46(3) (2012), 355–399.
DOI: 10.1051/ita/2012010.

- Work identity: https://doi.org/10.1051/ita/2012010
- Canonical source: https://www.numdam.org/item/ITA_2012__46_3_355_0/
- Local artifact: `cassaigne-nicolas-2012-semigroup-freeness.pdf`
- Version and status: peer-reviewed journal version, 45 pages
- Retrieved: 2026-08-30
- SHA-256: `d664f25c4ad174e260d0584e89ebe769f89a9053834f1e5c1873fc26d7dffcbb`
- Access and retention: publisher PDF distributed by NUMDAM; no open license identified
- Synopsis basis: bounded full-text inspection of the abstract, matrix-freeness sections,
  Example 6.6, and references

## Synopsis

The paper develops reductions and decision boundaries for code and freeness problems over
semigroups, with particular attention to multiplicative matrix semigroups. For a finite subset
`X` of a semigroup, freeness asks whether every generated element has at most one factorization
over `X`. The paper relates variants of this problem across matrix domains and records both
decidable strata and open fixed-generator cases.

For `D_λ=[[λ,0],[0,1]]` and `T_λ=[[λ,1],[0,1]]`, Example 6.6 sets
`D=D_(2/3)` and `T=T_(3/5)` and records the relation

```text
D T^10 D^2 T D^2 T D^10
= T^2 D^6 T^2 D^2 T D T D T D^2 T^2 D^2 T D T^2.
```

Both sides equal

```text
[[32768/6591796875, 242996824/146484375], [0, 1]].
```

The example attributes the relation and the absence of a shorter nontrivial equation to
Gawrychowski, Gutan, and Kisielewicz, *Theoretical Computer Science* 411 (2010), 1115–1120.

## Source Assessment

The retained object is the peer-reviewed journal PDF supplied by NUMDAM. No correction or
retraction was found. The project relies only on the displayed equality, which is independently
checked over `ℚ` in Lean; it does not rely on the cited minimality claim.

## Project Use

Prefixing the displayed relation by `T` and factoring both sides into blocks `T D^m` gives two
length-thirteen schedules for the mixed-prime shell. Local execution order reverses the printed
block order:

```text
[10,2,2,0,0,0,0,0,0,0,0,0,1]
= [0,0,1,2,0,2,1,1,2,0,6,0,0].
```

Conjugation by `z=5u` sends `T D^m` to
`T_m(u)=(1+3u(2/3)^m)/5`. `PeriodicShell.shellRun_benchmarkRelation` checks the resulting global
affine equality, and `PeriodicShell.benchmarkRelationCycle` checks that both distinct schedules
form all-unit cycles from their common rational periodic source. The generic
`PeriodicShell.shellPrefixesUnit_iff` and its consequence
`PeriodicShell.benchmarkRelationContextGuard` check that substituting the relation in any word
context preserves every intermediate shell guard.
