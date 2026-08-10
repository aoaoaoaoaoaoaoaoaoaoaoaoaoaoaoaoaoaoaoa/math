# Lozin and Zamaraev (2024): Union-closed sets and Horn Boolean functions

**Citation.** Vadim Lozin and Viktor Zamaraev, “Union-closed sets and Horn Boolean
functions,” *Journal of Combinatorial Theory, Series A* 202 (2024), article 105818.

- Work identity: DOI [`10.1016/j.jcta.2023.105818`](https://doi.org/10.1016/j.jcta.2023.105818)
- Canonical source: https://wrap.warwick.ac.uk/id/eprint/180696/
- Local artifact: `lozin-zamaraev-2024-frankl-horn-functions.pdf`
- Version and status: final peer-reviewed open-access publication
- Retrieved: 2026-08-08
- SHA-256: `c785bd2fb22b109d59d6c3e939d4b01acd7622d4ce2d558ff4c85d53714796d2`
- Access and retention: CC BY 4.0, stated on the article and repository record
- Synopsis basis: complete full-text inspection of the nine-page article

## Synopsis

The paper translates Frankl’s conjecture into Boolean-function language. A Boolean
function is Horn exactly when its false points are closed under coordinatewise conjunction,
so the conjecture becomes the assertion that every Horn function with at least two false
points has a variable occurring in at most half of them. Such a variable equivalently occurs
in at least half of the true points and is called *good*.

The authors prove the conjecture for submodular Boolean functions (Theorem 3). After
contracting strongly connected components of a quadratic pure-Horn implicant graph, a sink
component supplies a good variable. They also prove it for every nontrivial Horn function
admitting a Horn DNF with the dependency property (Theorem 4): for each variable `x`, one
variable `d(x)` occurs positively in every term in which `x` occurs negatively. An explicit
injection from zero entries to one entries in the true-point matrix establishes the result.
Double Horn functions are a special case.

The concluding section identifies bidual Horn functions, whose false points are
intersection-closed and whose true points are union-closed, as the next structural class.
It singles out self-dual Horn functions as a proposed core case. These statements are a
research direction, not a reduction of the general conjecture to that class.

## Source Assessment

The Horn equivalence and the two class theorems are proved in full. The proposed importance of
bidual and self-dual Horn functions is explicitly conjectural: the paper neither proves Frankl
for those classes nor proves that an arbitrary counterexample can be transformed into one. The
stated open status of those subclasses overlooks a short consequence of Karpas’s 2017
half-cube theorem: the larger of the union-closed true family and the set-complement of the
intersection-closed false family supplies a good variable. No correction or later version was
found during the present inspection.

## Project Use

The exact Horn translation and the dependency-property injection constrain the Boolean attack;
the bidual/self-dual proposal is the target of the density-dichotomy audit.
