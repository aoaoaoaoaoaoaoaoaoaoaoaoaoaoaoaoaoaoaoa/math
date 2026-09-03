import MatrixMortality.CHHNPrefixPacking
import MatrixMortality.Undecidability.Problems

/-!
# Prefix-packed mortality problems

The two concrete CHHN prefix codes turn every encoded `M₃(5)` instance into equivalent
`M₆(3)` and `M₁₂(2)` instances by primitive-recursive maps.
-/

namespace MatrixMortality.Undecidability

/-- Three `6 × 6` matrices obtained by the two-state ternary prefix packing. -/
def mortality63Pack (source : Mortality35) : Mortality63 :=
  fun label => Matrix.reindex finProdFinEquiv finProdFinEquiv
    (CHHNPrefixPacking.ternaryPack source label)

/-- Two `12 × 12` matrices obtained by the four-state binary prefix packing. -/
def mortality122Pack (source : Mortality35) : Mortality122 :=
  fun label => Matrix.reindex finProdFinEquiv finProdFinEquiv
    (CHHNPrefixPacking.binaryPack source (finTwoEquiv label))

private theorem mortality63Pack_entry_primrec (label : Fin 3) (row column : Fin 6) :
    Primrec fun source : Mortality35 => mortality63Pack source label row column := by
  let packedRow := (finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm row
  let packedColumn := (finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm column
  have row_fst :
      ((finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm row).1 =
        @Fin.divNat 2 3 row := rfl
  have column_fst :
      ((finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm column).1 =
        @Fin.divNat 2 3 column := rfl
  have packedRow_snd : packedRow.2 = @Fin.modNat 2 3 row := rfl
  have packedColumn_fst : packedColumn.1 = @Fin.divNat 2 3 column := rfl
  have packedColumn_snd : packedColumn.2 = @Fin.modNat 2 3 column := rfl
  by_cases routed : CHHNPrefixPacking.ternaryFiveCode.next packedRow.1 label = packedColumn.1
  · cases emitted : CHHNPrefixPacking.ternaryFiveCode.emission packedRow.1 label with
    | none =>
        exact (Primrec.const (if packedRow.2 = packedColumn.2 then 1 else 0)).of_eq
          fun source => by
            simp [mortality63Pack, CHHNPrefixPacking.ternaryPack,
              PrefixPacking.CompleteCode.machine, PrefixPacking.CompleteCode.output,
              WeightedTransducer.generator, packedRow, packedColumn, routed, emitted,
              packedRow_snd, packedColumn_fst, packedColumn_snd, Matrix.one_apply]
    | some sourceLabel =>
        exact (MortalityProblem.entry_primrec sourceLabel packedRow.2 packedColumn.2).of_eq
          fun source => by
            simp [mortality63Pack, CHHNPrefixPacking.ternaryPack,
              PrefixPacking.CompleteCode.machine, PrefixPacking.CompleteCode.output,
              WeightedTransducer.generator, packedRow, packedColumn, routed, emitted,
              packedRow_snd, packedColumn_fst, packedColumn_snd]
  · have routed' :
        CHHNPrefixPacking.ternaryFiveCode.next
            (@Fin.divNat 2 3 row) label ≠
          @Fin.divNat 2 3 column := by
      simpa [packedRow, packedColumn] using routed
    exact (Primrec.const 0).of_eq fun source => by
      simp [mortality63Pack, CHHNPrefixPacking.ternaryPack,
        PrefixPacking.CompleteCode.machine, WeightedTransducer.generator,
        row_fst, column_fst, routed']

private theorem mortality122Pack_entry_primrec (label : Fin 2) (row column : Fin 12) :
    Primrec fun source : Mortality35 => mortality122Pack source label row column := by
  let packedRow := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).symm row
  let packedColumn := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).symm column
  let letter := finTwoEquiv label
  have row_fst :
      ((finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).symm row).1 =
        @Fin.divNat 4 3 row := rfl
  have column_fst :
      ((finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).symm column).1 =
        @Fin.divNat 4 3 column := rfl
  have packedRow_snd : packedRow.2 = @Fin.modNat 4 3 row := rfl
  have packedColumn_fst : packedColumn.1 = @Fin.divNat 4 3 column := rfl
  have packedColumn_snd : packedColumn.2 = @Fin.modNat 4 3 column := rfl
  by_cases routed : CHHNPrefixPacking.binaryFiveCode.next packedRow.1 letter = packedColumn.1
  · cases emitted : CHHNPrefixPacking.binaryFiveCode.emission packedRow.1 letter with
    | none =>
        exact (Primrec.const (if packedRow.2 = packedColumn.2 then 1 else 0)).of_eq
          fun source => by
            simp [mortality122Pack, CHHNPrefixPacking.binaryPack,
              PrefixPacking.CompleteCode.machine, PrefixPacking.CompleteCode.output,
              WeightedTransducer.generator, packedRow, packedColumn, letter, routed, emitted,
              packedRow_snd, packedColumn_fst, packedColumn_snd, Matrix.one_apply]
    | some sourceLabel =>
        exact (MortalityProblem.entry_primrec sourceLabel packedRow.2 packedColumn.2).of_eq
          fun source => by
            simp [mortality122Pack, CHHNPrefixPacking.binaryPack,
              PrefixPacking.CompleteCode.machine, PrefixPacking.CompleteCode.output,
              WeightedTransducer.generator, packedRow, packedColumn, letter, routed, emitted,
              packedRow_snd, packedColumn_fst, packedColumn_snd]
  · have routed' :
        CHHNPrefixPacking.binaryFiveCode.next
            (@Fin.divNat 4 3 row) (finTwoEquiv label) ≠
          @Fin.divNat 4 3 column := by
      simpa [packedRow, packedColumn, letter] using routed
    exact (Primrec.const 0).of_eq fun source => by
      simp [mortality122Pack, CHHNPrefixPacking.binaryPack,
        PrefixPacking.CompleteCode.machine, WeightedTransducer.generator,
        row_fst, column_fst, routed']

/-- The `M₃(5) → M₆(3)` packing is primitive recursive. -/
theorem mortality63Pack_primrec : Primrec mortality63Pack :=
  MortalityProblem.primrec mortality63Pack mortality63Pack_entry_primrec

/-- The `M₃(5) → M₁₂(2)` packing is primitive recursive. -/
theorem mortality122Pack_primrec : Primrec mortality122Pack :=
  MortalityProblem.primrec mortality122Pack mortality122Pack_entry_primrec

/-- The ternary packing preserves and reflects mortality. -/
theorem mortality63Pack_mortal_iff (source : Mortality35) :
    (mortality63Pack source).Mortal ↔ source.Mortal := by
  unfold MortalityProblem.Mortal
  rw [show (mortality63Pack source).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv ∘
        CHHNPrefixPacking.ternaryPack source by rfl]
  rw [isMortal_reindex_iff]
  exact CHHNPrefixPacking.ternaryPack_isMortal_iff source

/-- The binary packing preserves and reflects mortality. -/
theorem mortality122Pack_mortal_iff (source : Mortality35) :
    (mortality122Pack source).Mortal ↔ source.Mortal := by
  unfold MortalityProblem.Mortal
  rw [show (mortality122Pack source).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv ∘
        (CHHNPrefixPacking.binaryPack source ∘ finTwoEquiv) by rfl]
  rw [isMortal_reindex_iff, isMortal_comp_equiv]
  exact CHHNPrefixPacking.binaryPack_isMortal_iff source

/-- Certified primitive-recursive reduction `M₃(5) ≤ M₆(3)`. -/
def mortality35To63 :
    PrimrecReduction (MortalityProblem.Mortal (d := 3) (k := 5))
      (MortalityProblem.Mortal (d := 6) (k := 3)) where
  emit := mortality63Pack
  emit_primrec := mortality63Pack_primrec
  target_iff_source := mortality63Pack_mortal_iff

/-- Certified primitive-recursive reduction `M₃(5) ≤ M₁₂(2)`. -/
def mortality35To122 :
    PrimrecReduction (MortalityProblem.Mortal (d := 3) (k := 5))
      (MortalityProblem.Mortal (d := 12) (k := 2)) where
  emit := mortality122Pack
  emit_primrec := mortality122Pack_primrec
  target_iff_source := mortality122Pack_mortal_iff

end MatrixMortality.Undecidability
