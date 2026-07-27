import MatrixMortality.Undecidability.NearyConverse
import MatrixMortality.Undecidability.TwoTagSource

/-!
# Verified restricted-tag sources

`NearyCompiler.compile` is the theorem-facing composition of Cook's one-hot cyclic compiler and
Neary's open-suffix restricted-tag compiler.  It turns any verified two-tag source into a
primitive-recursive family satisfying the arithmetic envelope and an exact arbitrary-execution
halting equivalence.  The proof is not an opaque correctness premise: its forward seam is
`read_exact_firing_halts`; its converse passes through `read_initialQueue`, `StableData`, and
the productive `GarbageBoundary` regime before `compiled_halts_implies_firing`.
-/

namespace MatrixMortality.Undecidability

/-- A fixed-width restricted binary-tag family recognizing a computable source predicate. -/
structure RestrictedTagSource (ι : Type*) [Primcodable ι] (accepts : ι → Prop) where
  /-- Deletion width shared by the emitted family. -/
  width : Nat
  /-- Variable appendant encoding one source input. -/
  body : ι → List TagLetter
  /-- The appendant compiler is primitive recursive. -/
  body_primrec : Primrec body
  /-- The deletion width lies in the terminal compiler's valid range. -/
  width_large : 2 < width
  /-- Every emitted appendant is long enough for the fixed boundary. -/
  body_long : ∀ index, width - 1 ≤ (body index).length
  /-- Every emitted appendant has the required terminal congruence. -/
  body_divisible : ∀ index, width - 1 ∣ (body index).length
  /-- Arbitrary restricted-tag termination is exactly source acceptance. -/
  halts_iff :
    ∀ index,
      TagHaltsFrom width (tagOutput (body index))
          ((body index).drop (width - 1) ++ [.b]) ↔
        accepts index

namespace NearyCompiler

/-- Compile a verified two-tag source through Cook and Neary without exposing either proof
engine at the endpoint seam. -/
noncomputable def compile {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) :
    RestrictedTagSource ι accepts where
  width := deletionWidth source.period
  body index :=
    body source.cyclicSystem (source.cyclicInput index) source.haltPhase source.period_pos
  body_primrec :=
    (body_primrec source.cyclicSystem source.haltPhase source.period_pos).comp
      source.cyclicInput_primrec
  width_large := deletionWidth_large source.period_pos
  body_long index := by
    simpa using
      NearyArithmeticEnvelope.body_long
        (arithmeticEnvelope source.cyclicSystem (source.cyclicInput index)
          source.haltPhase source.period_pos)
  body_divisible index := by
    simpa using
      NearyArithmeticEnvelope.body_divisible
        (arithmeticEnvelope source.cyclicSystem (source.cyclicInput index)
          source.haltPhase source.period_pos)
  halts_iff index := by
    constructor
    · intro halts
      have compiledHalts :
          TagHaltsFrom (deletionWidth source.period)
            (compiledOutput source.cyclicSystem (source.cyclicInput index)
              source.haltPhase source.period_pos)
            ((body source.cyclicSystem (source.cyclicInput index)
                source.haltPhase source.period_pos).drop
                (deletionWidth source.period - 1) ++ [.b]) := by
        rw [compiledOutput_eq_tagOutput]
        exact halts
      obtain ⟨firing, reach, fires⟩ :=
        compiled_halts_implies_firing source.cyclicSystem (source.cyclicInput index)
          source.haltPhase source.period_pos (source.cyclicInput_nonempty index)
          source.appendant_nonempty_at_zero compiledHalts
      exact source.accepts_of_avoidingFiring index firing reach fires
    · intro accepted
      have compiled :=
        read_exact_firing_halts source.cyclicSystem (source.cyclicInput index)
          source.haltPhase source.period_pos (source.cyclicInput_nonempty index)
          source.haltPhase_nonzero source.appendant_nonempty_at_zero
          (source.accepts_implies_exactFiring index accepted)
      rw [compiledOutput_eq_tagOutput] at compiled
      exact compiled

end NearyCompiler
end MatrixMortality.Undecidability
