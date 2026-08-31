import MatrixMortality.SeparatedTwoCOrbit

/-!
# Halting residue classes in the separated two-c family

For the coupled width-three family `qₙ = bb c bⁿ c bⁿ`, the residue classes zero and one
modulo three are periodic. This file begins the complementary halting classification. When
`n = 9k+8`, an exact history contains four `c`-headed strokes; its final queue has only `b`
at deletion-block heads and therefore drains.
-/

namespace MatrixMortality

namespace SeparatedTwoCResidue

open PeriodicHistory SeparatedTwoCOrbit Undecidability

@[simp] private theorem replicate_b_append_nested
    (left right : Nat) (tail : List TagLetter) :
    List.replicate left TagLetter.b ++
        (List.replicate right TagLetter.b ++ tail) =
      List.replicate (left + right) TagLetter.b ++ tail := by
  rw [← List.append_assoc, List.replicate_append_replicate]

private def eightResidueHistory (k : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate (3 * k + 2) strokeBBB ++ [strokeCBB] ++
    List.replicate (3 * k + 3) strokeBBB ++ [strokeCBB] ++
      List.replicate (3 * k + 2) strokeBBB ++ [strokeCBB]

private def eightResidueFinal (k : Nat) : List TagLetter :=
  bRun (12 * k + 9) ++ ([.b, .b, .c] ++
    (bRun (9 * k + 6) ++ ([.b, .b, .c] ++
    (bRun (12 * k + 12) ++ ([.b, .b, .c] ++
    (bRun (9 * k + 6) ++ ([.b, .b, .c] ++
    (bRun (12 * k + 12) ++ ([.b, .c, .b] ++
    (bRun (9 * k + 6) ++ ([.b, .c, .b] ++
      bRun (9 * k + 8))))))))))))

private theorem consumed_append_exact (left right : List (Stroke TagLetter 3)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed]

@[simp] private theorem produced_append (output : TagLetter → List TagLetter)
    (left right : List (Stroke TagLetter 3)) :
    produced output (left ++ right) = produced output left ++ produced output right := by
  simp [produced]

private theorem eightResidueHistory_equation (k : Nat) :
    consumed (eightResidueHistory k) ++ eightResidueFinal k =
      coupledInitial (9 * k + 8) ++
        produced (tagOutput (separatedBody (9 * k + 8))) (eightResidueHistory k) := by
  simp [eightResidueHistory, eightResidueFinal, coupledInitial, separatedBody, bRun, strokeCBB,
    stroke₃, Stroke.letters, tagOutput, nearyBody, List.append_assoc]
  have shortRun : 3 * (3 * k + 2) + 1 + 1 = 9 * k + 8 := by omega
  have longRun : 3 * (3 * k + 3) + 1 + 1 = 9 * k + 8 + 1 + 1 + 1 := by omega
  have firstBridge :
      12 * k + 9 + 1 + 1 + 1 + 1 = 9 * k + 8 + 1 + (3 * k + 2 + 1 + 1) := by
    omega
  have outerRun : 9 * k + 6 + 1 + 1 = 9 * k + 8 := by omega
  have middleBridge :
      12 * k + 12 + 1 + 1 = 9 * k + 8 + 1 + (3 * k + 3 + 1 + 1) := by
    omega
  rw [shortRun, longRun, middleBridge, firstBridge, outerRun]

private theorem clean_bbc : ConstantAtMultiples 3 TagLetter.b
    [TagLetter.b, TagLetter.b, TagLetter.c] := by
  intro index index_lt index_aligned
  simp only [List.length_cons, List.length_nil] at index_lt
  have index_zero : index = 0 := by omega
  subst index
  rfl

private theorem clean_bcb : ConstantAtMultiples 3 TagLetter.b
    [TagLetter.b, TagLetter.c, TagLetter.b] := by
  intro index index_lt index_aligned
  simp only [List.length_cons, List.length_nil] at index_lt
  have index_zero : index = 0 := by omega
  subst index
  rfl

private theorem eightResidueFinal_clean (k : Nat) :
    ConstantAtMultiples 3 TagLetter.b (eightResidueFinal k) := by
  unfold eightResidueFinal
  refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
  · refine ConstantAtMultiples.append clean_bbc ?_ (by decide)
    refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
    · refine ConstantAtMultiples.append clean_bbc ?_ (by decide)
      refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
      · refine ConstantAtMultiples.append clean_bbc ?_ (by decide)
        refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
        · refine ConstantAtMultiples.append clean_bbc ?_ (by decide)
          refine ConstantAtMultiples.append
            (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
          · refine ConstantAtMultiples.append clean_bcb ?_ (by decide)
            refine ConstantAtMultiples.append
              (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
            · refine ConstantAtMultiples.append clean_bcb
                (ConstantAtMultiples.replicate 3 _ TagLetter.b) (by decide)
            · simp only [bRun, List.length_replicate]
              exact ⟨3 * k + 2, by omega⟩
          · simp only [bRun, List.length_replicate]
            exact ⟨4 * k + 4, by omega⟩
        · simp only [bRun, List.length_replicate]
          exact ⟨3 * k + 2, by omega⟩
      · simp only [bRun, List.length_replicate]
        exact ⟨4 * k + 4, by omega⟩
    · simp only [bRun, List.length_replicate]
      exact ⟨3 * k + 2, by omega⟩
  · simp only [bRun, List.length_replicate]
    exact ⟨4 * k + 3, by omega⟩

private theorem halts_of_history (output : TagLetter → List TagLetter)
    (priorHistory : List (Stroke TagLetter 3)) (source target : List TagLetter)
    (target_halts : TagHaltsFrom 3 output target)
    (equation : consumed priorHistory ++ target = source ++ produced output priorHistory) :
    TagHaltsFrom 3 output source := by
  obtain ⟨suffix, short, short_length, suffix_eq⟩ :=
    history_of_tagHaltsFrom output target_halts
  apply tagHaltsFrom_of_history output (priorHistory ++ suffix) source short short_length
  rw [consumed_append_exact, produced_append]
  simp only [List.append_assoc]
  calc
    consumed priorHistory ++ (consumed suffix ++ short) =
        consumed priorHistory ++ (target ++ produced output suffix) := by rw [suffix_eq]
    _ = (consumed priorHistory ++ target) ++ produced output suffix := by
      simp [List.append_assoc]
    _ = (source ++ produced output priorHistory) ++ produced output suffix := by
      rw [equation]
    _ = source ++ (produced output priorHistory ++ produced output suffix) := by
      simp [List.append_assoc]

/-- The coupled diagonal input with separation `n=9k+8` has a four-`c` halting certificate. -/
theorem eightResidue_tagHaltsFrom (k : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (9 * k + 8)))
      (coupledInitial (9 * k + 8)) := by
  have final_halts := tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (9 * k + 8))) TagLetter.b rfl
    (eightResidueFinal k) (eightResidueFinal_clean k)
  exact halts_of_history (tagOutput (separatedBody (9 * k + 8))) (eightResidueHistory k)
    (coupledInitial (9 * k + 8)) (eightResidueFinal k) final_halts
    (eightResidueHistory_equation k)

end SeparatedTwoCResidue

end MatrixMortality
