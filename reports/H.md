# H. Internalizing the Halava–Niskanen integrality test

Verdict: discovered

Cells affected: none; `M₃(k)` and `M₄(k)` remain open.

Lean: none.

Statement: For Halava–Niskanen’s fixed-machine encoding, all denominators are powers of the
radix `n`; the letter-code primes occur only in numerators. Hence offending primes are bounded by
`{p : p ∣ n}`, and one may choose a prime radix `n=π>∏pᵢ`. A wrong right-symbol guess first
appears in `(3,2)` as `σ(#vᴿ)+(σ(c)−σ(d))/π`; a wrong left state-symbol guess appears in `(3,1)`
as an analogous digit difference divided by `π`. Boundary and endpoint misuse also exposes
negative radix powers in diagonal and lower-row entries.

`MM-C06` compresses factored cuts but supplies no memory of prefix integrality. Fixed finite
unary weights would also bound denominator primes; position-indexed prime weights would make
them run-dependent, and any unary encoding retaining inverse `π`-shifts retains the healing.

Obstacle: Even with `n=π`, radix-pop generators contain `π⁻¹`, while boundary and identity
generators have nonunit determinants, and an opposite push heals the poison by
`π(t+(c−d)/π)+b=πt+c−d+b∈ℤ`; thus neither `MM-C01` nor a `π`-integral scalar endpoint excludes
illegal words without a new monotone coordinate or a non-radix tape encoding.

Discovered: Published Lemma 6 is false as stated. It allows arbitrary
`α=∑zᵢσ(sᵢ)`, so `α=σ((q,a))−σ(b)+σ(c)` satisfies its allegedly impossible equation. With digit
images `35S,21S,15S`, where `S` is the product of the remaining digit primes, `α=29S` is not a
digit image yet `29S−35S+21S=15S`. Because Lemma 5 and
Theorems 7, 8, and 11 depend on it, the paper’s main claims retain a proof gap unless reachable
coefficients obey an unstated stronger invariant.

DAG metadata:

- `H-O01`: obstruction / literature plus exact rational computation / audited / active.
- `H-D01`: source correction / literature audit plus exact counterexample / audited / active.

Next:

- Resolve GitHub issue `#15`: recover Lemma 6’s intended ancestry restriction or refute it.
- Seek a finite-dimensional monotone poison channel independent of the radix shift modes.
