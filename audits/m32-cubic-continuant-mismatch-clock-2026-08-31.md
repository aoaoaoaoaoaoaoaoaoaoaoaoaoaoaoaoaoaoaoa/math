# M₃(2) Cubic Continuant Mismatch-Clock Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S58` supplies positive readers for both letters of the fixed cubic radix stack, but a
false-for-true error and a true-for-false error are opposite upper translations. Without another
state change, the two errors cancel projectively and defeat terminal equality tests.

## Contracting Clock

For a guessed and written bit, assign the error

```text
e(false,false)=0,  e(false,true)=−1,
e(true,false)=1,   e(true,true)=0.
```

The normalized reader-writer pair is `25U((125/48)e)`. Append the true radix writer after every
pair. Its diagonal ratio is `4/25`. After `n` checks, append `n` true-readers. Lean proves that
the resulting normalized product is

```text
U((125/48)D(e₀,…,eₙ₋₁)),
D([])=0,  D(e::es)=e+(4/25)D(es).
```

The physical proof composes the reader and writer certificates together with their explicit
nonzero rational scales. Every wait in every reader, writer, clock, and cleanup block is
strictly positive.

## Signed-Radix Injectivity

Define the cleared integer code

```text
C([])=0,
C(e::es)=e·25^|es|+4C(es).
```

Lean checks `D(es)=25C(es)/25^|es|`. If every digit lies in `{−1,0,1}` and `C(es)=0`, reduction
modulo four forces the head digit to vanish because `25^k≡1 (mod 4)`. Division by four and
induction then force every remaining digit to vanish. The error table converts this statement
to equality of every guessed/written pair.

## Endpoint Detector

Splitting the previously known endpoint bridge after its first positive wait gives the exact
matrix identity

```text
M₀M₁₂ U(s) M₁₂M₈M₁₂M₁₂M₁₅M₈M₀
  = (−60369430118400000s)M₀.
```

The matrix `M₀` is nonzero, so this sandwich vanishes exactly when `s=0`. Combining the detector
with the clocked and cleaned comparison proves that the full physical word

```text
[0,12] · checks · true-readersⁿ · [12,8,12,12,15,8,0]
```

vanishes exactly when every guess equals its writer.

## Adjudication

| Claim | Judgment |
| --- | --- |
| each normalized error is exactly `0` or `±125/48` | Lean checked |
| the common clock weights successive errors by `4/25` | Lean checked |
| the cleared signed radix code is injective on `{−1,0,1}` digits | Lean checked |
| the balanced physical checker realizes the signed defect translation | Lean checked |
| every interior physical wait is positive | Lean checked |
| the split endpoint bridge detects the defect exactly | Lean checked |
| the designated endpoint word is zero exactly on matching checks | Lean checked |
| every arbitrary zero word has the designated block grammar | open |
| the complete fixed cubic continuant language or `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: cancellation of opposite read errors in a designated comparison spelling
GAINED: a positive clocked binary comparator with an exact physical zero detector
EXPOSED: the global arbitrary-word grammar/converse as the remaining compiler obligation
NEXT: force every zero witness into complete clocked blocks, or trap every malformed spelling
```
