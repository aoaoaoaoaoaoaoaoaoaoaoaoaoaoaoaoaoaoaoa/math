# M₄(3) periodic-conjugate scanner decision audit

**Date:** 10 August 2026

**Status:** exact promised decision reconstructed; `C` retired; not Lean-formalized

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide the last kernel of the promised positive overlap-queue trunk

## Verdict

The report survives hostile reconstruction. Let `A=0s`, with nonempty `s`, and let nonempty
`P` satisfy

```text
A P = K A.
```

In rule state `R`, the scanner loops on `c` while appending `P` and enters erase state `E` on
`¬c` while appending `U`. In `E`, it deletes `a` and returns on `¬a` while appending `W A`.
Among instances promised never to reach `(R,A)`, acceptance from `(R,s)` is decidable by one
finite first-return calculation and at most `#₁(K)` zero-gap tests. This retires `C`. Together
with `M4-D01` and `M4-D02`, it closes the exhaustive source class `M4-S05`; it does not decide
`M₄(3)`.

The empty-queue promise is automatic: every transition remaining in `R` appends nonempty `P`,
and every transition entering `R` appends nonempty `A`. Avoidance of `(R,A)` is substantive and
is used once in the decision proof.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`5cb071fa338f46b484f21764d2df4ba4d2bc0227`. Its transient final report has SHA-256 digest
`0fc0ce473e1913890a309c03b47de90900addb0629166f8d6b8a39daeed10dfc`.

## Exact Classifier

First compute the initial `R` phase without orbit search. If `s=cᵗ(¬c)Z`, its first `E` queue
is `Z Pᵗ U`. If `s=cᴸ`, then either `P∈c⁺` and `R` never exits, or, uniquely writing
`P=cʰ(¬c)Z`, the first `E` queue is `Z P^(L+h−1) U`. An all-`a` queue accepts immediately;
otherwise its first `¬a` makes the first return.

After a return, every promised accepting computation is forced into

```text
a=c=0,    A∈0⁺,    U∈0*,    W∈0*.
```

Put `p=#₁(K)`. Reject if `p=0` or `p` is even. For odd `p`, scan `K²` and let `γᵣ` be the
number of zeros immediately preceding its `r`th `1`. Define

```text
t₁ = γ₁ − 1,
tᵢ = γ_(2i−1)       for 2≤i≤p,
Tᵢ = t₁+⋯+tᵢ.
```

The scanner accepts after the return exactly when

```text
p Tᵢ = 2i−1
```

for some `1≤i≤p`. Thus every operation is finite in the supplied words.

## Reconstruction

The conjugacy equation has the complete primitive normal form

```text
K=qᵈ,    q=xy,    P=(yx)ᵈ,    A=qʳx,
```

where `q` is primitive and `x` is its canonical proper prefix. This includes the empty cut and
all nonprimitive powers.

Use frames `z_E=ε` and `z_R=A`. For every actual trace prefix consuming `h` and reaching
control state `σ` with queue `Q`, direct induction on the four scanner roles gives

```text
0 h Q = C(h) z_σ,
```

where the chronological cancellation words for `(E,a)`, `(E,¬a)`, `(R,c)`, and `(R,¬c)` are
respectively `ε`, `W`, `K`, and `AU`. Because this identity holds at actual prefixes, it
includes queues consuming symbols appended earlier in the same phase; no pristine-block premise
enters.

Counting the bit opposite `a` first eliminates `c=¬a`: every acceptance there is already a
no-return acceptance. When `c=a`, the same count, followed by the forbidden `(R,A)` case,
forces `a=c=0` and unary-zero `A,U`. A parity-and-gap count in the full telescope identity
forces unary-zero `W`. If the primitive root `q` is unary, rule state loops forever. Otherwise
`A=0ᴺ` is the primitive cut, so `q=Ay`, `K=(Ay)ᵈ`, and `P=(yA)ᵈ` for a word `y` containing
`1`.

For an accepting trace with `i`th rule-phase loop count `tᵢ`, the prefix identity immediately
before its `R→E` transition says that the queue begins at the `(2i−1)`st `1` of the right-hand
side. The first `p` sampled odd gaps traverse every cyclic one-gap of `K`; no completed spacer
can align in this first traversal, and only the first sample carries the initial-frame
correction. Hence the displayed finite values of `tᵢ`, and

```text
Δᵢ = p Tᵢ − (2i−1)
```

is exactly the number of ones left upon entering `E`. The first nonpositive `Δᵢ` in the first
`p` phases is zero. If all are positive, each later block of `p` phases adds all `#₀(K)` cyclic
zeros and a nonnegative number of complete unary spacers. Since `#₀(K)≥|A|≥2`, its affine
block counter is nondecreasing, and every later `Δ` is strictly larger than its first-block
counterpart. Acceptance therefore cannot first occur later.

## Adversarial Checks

The reconstruction explicitly covers:

- both identifications `c=a` and `c=¬a`;
- every solution of `AP=KA`, including nonprimitive powers and empty-cut degeneracies;
- infinite initial rule phases, early acceptance, empty `U` or `W`, and unary `P`;
- self-consumption of newly appended production and queues shorter than a nominal phase;
- arbitrary malformed intermediate queues and exact FIFO order;
- the exact use, rather than silent strengthening, of the `(R,A)` avoidance promise.

An independent exact simulator enumerated 124 small conjugacy solutions and tested 6,464
deterministic and seeded-random instances. It found no mismatch in the 1,235 promised cases
whose orbit halted or cycled within the bound; 5,145 growth-cutoff cases were left unresolved.
A second targeted pass checked all 7,276 promised classifier-positive instances with
`|U|,|W|≤3` over the same conjugacy set and found an accepting trace in every case. Cutoffs and
unpromised instances were not counted as evidence.

## Promotion Boundary

Promoted:

- the exact promised decision procedure;
- the primitive conjugacy normal form and prefix telescope;
- the finite odd-gap quotient and monotone later-block exclusion;
- retirement of `C` and closure of the `M4-S05` source trunk.

Not promoted:

- scanner-specific Lean infrastructure whose only consumer would be this retired route;
- raw simulator code or the external report;
- an unconditional theorem without `(R,A)` avoidance;
- any claim that the surviving parabolic matrix trunk is decidable.

The zero-line choice is deliberate. The result removes the final consumer of this scanner
semantics, while the exact proof and its promise boundary are preserved here. New Lean code
would enlarge a dead lane without strengthening the master reduction.

## Remaining Frontier

All positive overlap-queue kernels allowed by `M4-S05` are decidable. The live `M₄(3)` frontier
is now the four-node parabolic matrix trunk: original semantic incidence, original oriented
transport, retuned right annihilation, and the retuned arbitrary-word converse.
