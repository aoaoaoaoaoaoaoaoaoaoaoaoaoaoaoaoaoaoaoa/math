# M₃(2) ReturnSquare Pure-Denominator Descent Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The p-adic pivot `R32-S53` leaves words whose proper-rest state carries the complete denominator
content at every denominator prime. Local valuation laws do not prevent that content from
recurring indefinitely. This audit tests the full rational affine inverse instead.

## Exact Coordinate

For denominator `B`, scale `t`, and target `s`, the pure-denominator inverse is

```text
P_t(s)=B(st−1)/(st+(B−1)t²−B).
```

For `B≥2`, `t≥4`, and `s≥−1`, the denominator is strictly positive. Direct polynomial
identities then prove

```text
P_t(s)≥−1,
P_t(s)>1  iff  s>t,
P_t(s)≤s−t+1  when s>t.
```

The last inequality is the descent tax. It is uniform in denominator content and becomes
stronger at larger waits.

## Projective Gate

The affine recurrence is not used heuristically. Lean proves by induction that the homogeneous
adjugate tail state is `(Run·S,S)` with `S>0`, where `Run` is the right-to-left affine inverse
run starting at `B`. Hence normalization loses neither a zero coordinate nor a common factor.
The separated-head incidence of a physical bridge zero cancels `S` and yields

```text
Run=q^(head+1).
```

## Global Bound

Every intermediate target on a successful inverse run must remain above one. Summing the
one-step descent gives

```text
q^(head+1)+Σ_wait∈tail(q^(wait+1)−1)≤B.
```

Two immediate consequences are formalized:

```text
q^(wait+1)<B                  for every wait in the tail,
q^(head+1)+|tail|(q−1)≤B.
```

These inequalities bound the head, every tail entry, and the tail length. The complete
pure-denominator search is finite, including the simultaneously shallow chamber.

## Scope

The rational theorem assumes `q≥4` and `B≥2`. It covers every positive composite integral base,
which in fact has `q≥6`; prime-power ReturnSquare already has an exact classification. This
certificate does not assert that every bounded solution is a one-return resonance. Exact finite
enumeration remains necessary.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| common denominator content can support an unbounded pure-denominator word | rejected | every inverse step pays at least its scale minus one |
| affine normalization may erase the obstruction | rejected | the homogeneous lower coordinate is strictly positive |
| the shallow pure-denominator chamber remains infinite | rejected | head, entries, and length all have explicit bounds |
| arbitrary-composite ReturnSquare is fully classified | open | the positive-numerator certificate and finite search still require assembly |

MASTER VERDICT: pure-denominator ReturnSquare is effectively finite

NEW WOUND: the last p-adically shallow common-content throat is closed

EXACT NEXT STEP: compose the positive-numerator and pure-denominator finite certificates

## Evidence

The formal owner is
[`ReturnSquarePureDenominatorDescent.lean`](../MatrixMortality/ReturnSquarePureDenominatorDescent.lean).
The focused module build, umbrella build, transitive axiom inspection, Lean LSP diagnostics,
forbidden-aperture scan, and whitespace gate passed at the recorded commit.
