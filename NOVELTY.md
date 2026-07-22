# Novelty Search Log

## Questions

1. Has a valid proof of `GPCP(4)` undecidability appeared?
2. Has a valid proof of `M₃(5)` undecidability appeared?
3. Is the fixed-width block-forcing repair of Neary's four ordinary pairs already known?
4. Is the fresh-marker terminal construction already used for this bounded PCP family?

Searches were run on 2026-07-21. Bibliographic nonexistence cannot be proved; this log records
the search surface and the strongest safe language.

## Channels Searched

- arXiv title, abstract, and full-metadata queries for matrix mortality, generalized Post
  correspondence, bounded GPCP, terminal PCP, and combinations with Neary and Rote;
- DBLP and Crossref title searches;
- OpenAlex and Semantic Scholar forward-citation graphs for CHHN14, HHH07, Neary13,
  Neary15, Nicolas08, and Rote24/25;
- exact web phrases `M_3(5)`, `M₃(5)`, `five 3 × 3 matrices`, `GPCP(4)`,
  `four-generator generalized Post correspondence`, `fixed terminal tile`, `fresh marker`,
  and `rank-one absorption`;
- backward references and terminology in the locally preserved papers.

No later indexed source was found claiming a valid five-generator `3 × 3` mortality bound or
four-generator GPCP undecidability. Nicolas08 and CHHN14 record `GPCP(4)` as open. Later
matrix-semigroup surveys retain the six-generator `3 × 3` bound. Rote24/25 recognizes and
uses Neary's forced terminal role for probabilistic automata, but does not state the bounded
GPCP or mortality consequences.

## Adjudicated Prior Art

### Same numerical statement, invalid proof

Neary's arXiv:1312.6700v1 (2013) explicitly announces undecidability for five `3 × 3` integer
matrices. It relies on the paper's abandoned four-pair PCP claim. The accepted STACS 2015
replacement proves five-pair PCP and derives only six `3 × 3` matrices. Therefore:

```text
“first public statement of M₃(5)” is false;
“first valid proof found” remains plausible.
```

### Rank-one absorption is established technique

Halava–Harju–Hirvensalo (2007), Theorem 10, absorbs forced endpoints into a rank-one
idempotent and proves a scalar-factor converse. CHHN's standard `GPCP(k) → Z₃(k) → M₃(k+1)`
compiler adds an outer product of boundary vectors. For the present right boundary it
specializes to `Ψ(10^β,ε)e₃e₁ᵀ`. The matrix mechanism is therefore prior art.

### Rote's terminal repair is diagnosis, not a dependency

Rote correctly identifies the flaw in Neary's four-one terminal guard and replaces it with a
long unary block. His proof does not classify every malformed prefix-comparable residual. The
new result neither attacks nor assumes the truth of that quantitative repair: it proves the
four-tile terminal equation directly and supplies a different fresh-marker fifth pair.

### Apparently new source argument

The new source theorem states, for Neary's exact restricted tag family:

```text
∃w over four labels, U(w)10^β = V(w)
  ↔ tag halting.
```

Its soundness mechanism is an exact zero-run automaton followed by a global queue-history
lemma. No audited source contains this argument. It simultaneously gives:

- four-generator GPCP undecidability;
- a corrected five-pair PCP theorem via a fresh delimiter and fixed-length binary code;
- the standard five-matrix mortality corollary.

The fresh-marker device is elementary enough that broad novelty should not be claimed without
an author query. The bounded source theorem and its application to the Neary family are the
substantive contribution.

## Later-Frontier Evidence

CHHN14 marks `M₃(5)` unknown. Neary15 derives the conventional six-generator consequence.
Bell–Potapov–Semukhin (MFCS 2019 / journal 2021) still report six `3 × 3` matrices as the
accepted bound. Dong's 2023 survey gives no sharper bounded-generator theorem. No indexed
forward citation of Neary15 or Rote25 found in the search made the `GPCP(4)` deduction.

## Safe Publication Language

Use:

> We give, to our knowledge, the first valid proof that binary-target `GPCP(4)` is undecidable
> and consequently the first valid derivation of `M₃(5)` undecidability. The latter numerical
> statement appeared earlier in a superseded preprint whose four-pair PCP premise was
> abandoned.

Do not use:

- “first statement of `M₃(5)`”;
- “new rank-one absorption method”;
- “Rote proved the source property exhaustively”;
- an unqualified priority claim before author review.

## Mandatory Human Queries

Send the revised proof to Günter Rote and Turlough Neary, explicitly asking about the
block-forcing soundness theorem and whether the fresh-marker correction has circulated. Ask
François Nicolas whether `GPCP(4)` is known under “modified PCP,” “individual correspondence
problem,” “fixed-boundary PCP,” or a convention counting boundary pairs. Ask at least one of
Vesa Halava, Tero Harju, Julien Cassaigne, or Mika Hirvensalo whether the five-matrix corollary
or structured promise is folklore.

Replies are stronger evidence than another database query and should be archived alongside the
preprint.
