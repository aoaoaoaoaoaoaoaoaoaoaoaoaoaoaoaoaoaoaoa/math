import MatrixMortality.NearyEncoding
import MatrixMortality.Undecidability.Problems

/-!
# Sparse width-three restricted tag bodies

For a restricted width-three body containing one `c`, the coupled Neary initial queue always
halts. The proof uses the exact arithmetic normal form of its unique surviving `c`: deleting
three leading `b`s preserves `i + 3j`, while firing the `c` divides a nonzero defect by three.
-/

namespace MatrixMortality
namespace WidthThreeSparseBody

/-- A run of `b` letters. -/
def bRun (length : Nat) : List TagLetter := List.replicate length .b

/-- A restricted tag body with exactly one `c`. -/
def sparseBody (left right : Nat) : List TagLetter :=
  bRun left ++ .c :: bRun right

private def sparseQueue (left right : Nat) : List TagLetter :=
  bRun left ++ .c :: bRun right

@[simp] theorem bRun_zero : bRun 0 = [] := rfl

@[simp] theorem bRun_succ (length : Nat) :
    bRun (length + 1) = .b :: bRun length := by
  exact List.replicate_succ

private theorem bRun_add (left right : Nat) :
    bRun (left + right) = bRun left ++ bRun right := by
  change List.replicate (left + right) TagLetter.b =
    List.replicate left TagLetter.b ++ List.replicate right TagLetter.b
  exact List.replicate_add left right TagLetter.b

private theorem bRun_snoc (length : Nat) :
    bRun (length + 1) = bRun length ++ [.b] :=
  List.replicate_succ'

private theorem bRun_tagStep (body : List TagLetter) (length : Nat) :
    TagStep 3 (tagOutput body) (bRun (length + 3)) (bRun (length + 1)) := by
  refine ⟨⟨.b, [.b, .b], rfl⟩, bRun length, ?_, ?_⟩
  · change bRun (length + 3) = [.b, .b, .b] ++ bRun length
    rw [show length + 3 = 3 + length by omega, bRun_add]
    rfl
  · change bRun (length + 1) = bRun length ++ [.b]
    exact bRun_snoc length

private theorem bRun_halts (body : List TagLetter) (length : Nat) :
    TagHaltsFrom 3 (tagOutput body) (bRun length) := by
  induction length using Nat.strong_induction_on with
  | h length induction =>
      by_cases short : length < 3
      · exact .stop <| by simpa [bRun] using short
      · have three_le : 3 ≤ length := Nat.le_of_not_gt short
        obtain ⟨tail, length_eq⟩ := Nat.exists_eq_add_of_le three_le
        rw [length_eq, Nat.add_comm] at induction ⊢
        apply TagHaltsFrom.step (bRun_tagStep body tail)
        exact induction (tail + 1) (by omega)

private theorem sparseQueue_step_three (body : List TagLetter) (left right : Nat) :
    TagStep 3 (tagOutput body) (sparseQueue (left + 3) right)
      (sparseQueue left (right + 1)) := by
  refine ⟨⟨.b, [.b, .b], rfl⟩, sparseQueue left right, ?_, ?_⟩
  · change sparseQueue (left + 3) right = [.b, .b, .b] ++ sparseQueue left right
    simp only [sparseQueue]
    rw [show left + 3 = 3 + left by omega, bRun_add]
    rfl
  · change sparseQueue left (right + 1) = sparseQueue left right ++ [.b]
    simp only [sparseQueue, List.append_assoc, List.cons_append]
    rw [bRun_snoc]

private theorem sparseQueue_step_one (body : List TagLetter) (right : Nat) :
    TagStep 3 (tagOutput body) (sparseQueue 1 (right + 1)) (bRun (right + 1)) := by
  refine ⟨⟨.b, [.c, .b], rfl⟩, bRun right, ?_, ?_⟩
  · simp [sparseQueue, bRun_succ, Stroke.letters]
  · change bRun (right + 1) = bRun right ++ [.b]
    exact bRun_snoc right

private theorem sparseQueue_step_two (body : List TagLetter) (right : Nat) :
    TagStep 3 (tagOutput body) (sparseQueue 2 right) (bRun (right + 1)) := by
  refine ⟨⟨.b, [.b, .c], rfl⟩, bRun right, ?_, ?_⟩
  · simp [sparseQueue, bRun, Stroke.letters]
  · change bRun (right + 1) = bRun right ++ [.b]
    exact bRun_snoc right

private theorem sparseQueue_step_c (left right tail : Nat) :
    TagStep 3 (tagOutput (sparseBody left right)) (sparseQueue 0 (tail + 2))
      (sparseQueue (tail + left) (right + 1)) := by
  refine ⟨⟨.c, [.b, .b], rfl⟩, bRun tail, ?_, ?_⟩
  · change sparseQueue 0 (tail + 2) = [.c, .b, .b] ++ bRun tail
    simp only [sparseQueue, bRun_zero, List.nil_append]
    rw [show tail + 2 = 2 + tail by omega, bRun_add]
    rfl
  · change sparseQueue (tail + left) (right + 1) =
      bRun tail ++ tagOutput (sparseBody left right) .c
    simp only [sparseQueue, sparseBody, tagOutput, nearyBody,
      List.append_assoc, List.cons_append]
    rw [bRun_add, bRun_snoc]
    simp [List.append_assoc]

private def sparseScale (left right : Nat) : Nat := left + 3 * right + 1

private theorem sparseQueue_halts_of_balance (bodyLeft bodyRight defect left right : Nat)
    (defect_pos : 0 < defect)
    (balance : 2 * (left + 3 * right) + defect =
      3 * sparseScale bodyLeft bodyRight) :
    TagHaltsFrom 3 (tagOutput (sparseBody bodyLeft bodyRight))
      (sparseQueue left right) := by
  induction defect using Nat.strong_induction_on generalizing left right with
  | h defect defect_induction =>
      induction left using Nat.strong_induction_on generalizing right with
      | h left left_induction =>
          by_cases three_le : 3 ≤ left
          · obtain ⟨nextLeft, left_eq⟩ := Nat.exists_eq_add_of_le three_le
            rw [left_eq, Nat.add_comm] at balance ⊢
            apply TagHaltsFrom.step
              (sparseQueue_step_three (sparseBody bodyLeft bodyRight) nextLeft right)
            apply left_induction nextLeft (by omega) (right + 1)
            omega
          · have left_lt : left < 3 := Nat.lt_of_not_ge three_le
            interval_cases left
            · by_cases right_short : right < 2
              · exact .stop <| by
                  simp [sparseQueue, bRun]
                  omega
              · obtain ⟨tail, right_eq⟩ := Nat.exists_eq_add_of_le
                  (Nat.le_of_not_gt right_short)
                rw [right_eq, Nat.add_comm] at balance ⊢
                let nextDefect := sparseScale bodyLeft bodyRight - 2 * (tail + 2)
                have defect_eq : defect = 3 * nextDefect := by
                  dsimp only [nextDefect]
                  omega
                have nextDefect_pos : 0 < nextDefect := by omega
                have nextDefect_lt : nextDefect < defect := by omega
                apply TagHaltsFrom.step
                  (sparseQueue_step_c bodyLeft bodyRight tail)
                apply defect_induction nextDefect nextDefect_lt
                  (tail + bodyLeft) (bodyRight + 1) nextDefect_pos
                dsimp only [sparseScale] at balance ⊢
                omega
            · by_cases right_zero : right = 0
              · subst right
                exact .stop <| by simp [sparseQueue, bRun]
              · obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero right_zero
                apply TagHaltsFrom.step
                  (sparseQueue_step_one (sparseBody bodyLeft bodyRight) tail)
                exact bRun_halts (sparseBody bodyLeft bodyRight) (tail + 1)
            · apply TagHaltsFrom.step
                (sparseQueue_step_two (sparseBody bodyLeft bodyRight) right)
              exact bRun_halts (sparseBody bodyLeft bodyRight) (right + 1)

/-- Every coupled restricted width-three queue whose body contains exactly one `c` halts. -/
theorem sparseBody_coupled_halts (left right : Nat) :
    TagHaltsFrom 3 (tagOutput (sparseBody left right))
      ((sparseBody left right).drop 2 ++ [.b]) := by
  by_cases left_small : left < 2
  · interval_cases left
    · by_cases right_zero : right = 0
      · subst right
        exact bRun_halts (sparseBody 0 0) 1
      · obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero right_zero
        have initial_eq :
            (sparseBody 0 (tail + 1)).drop 2 ++ [.b] = bRun (tail + 1) := by
          simp only [sparseBody, bRun_zero, List.nil_append, bRun_succ]
          exact (bRun_snoc tail).symm
        rw [initial_eq]
        exact bRun_halts (sparseBody 0 (tail + 1)) (tail + 1)
    · have initial_eq :
          (sparseBody 1 right).drop 2 ++ [.b] = bRun (right + 1) := by
        simp only [sparseBody, bRun_succ, bRun_zero]
        exact (bRun_snoc right).symm
      rw [initial_eq]
      exact bRun_halts (sparseBody 1 right) (right + 1)
  · obtain ⟨initialLeft, left_eq⟩ := Nat.exists_eq_add_of_le
      (Nat.le_of_not_gt left_small)
    rw [left_eq, Nat.add_comm]
    have initial_eq :
        (sparseBody (initialLeft + 2) right).drop 2 ++ [.b] =
          sparseQueue initialLeft (right + 1) := by
      change (bRun (initialLeft + 2) ++ .c :: bRun right).drop 2 ++ [.b] =
        bRun initialLeft ++ .c :: bRun (right + 1)
      rw [show initialLeft + 2 = 2 + initialLeft by omega, bRun_add, bRun_snoc right]
      change ([TagLetter.b, TagLetter.b] ++ bRun initialLeft ++
          TagLetter.c :: bRun right).drop 2 ++ [TagLetter.b] =
        bRun initialLeft ++ TagLetter.c :: (bRun right ++ [TagLetter.b])
      simp [List.append_assoc]
    rw [initial_eq]
    let scale := sparseScale (initialLeft + 2) right
    apply sparseQueue_halts_of_balance (initialLeft + 2) right scale initialLeft (right + 1)
    · simp [scale, sparseScale]
    · simp [scale, sparseScale]
      omega

private theorem eq_bRun_of_count_c_zero (word : List TagLetter)
    (count_zero : word.count .c = 0) : word = bRun word.length := by
  induction word with
  | nil => rfl
  | cons head tail induction =>
      cases head with
      | b =>
          have tail_zero : tail.count .c = 0 := by simpa using count_zero
          rw [induction tail_zero]
          rw [show (TagLetter.b :: bRun tail.length).length = tail.length + 1 by
            simp [bRun]]
          exact (bRun_succ tail.length).symm
      | c => simp at count_zero

private theorem eq_sparseBody_of_count_c_one (word : List TagLetter)
    (count_one : word.count .c = 1) :
    ∃ left right, word = sparseBody left right := by
  have c_mem : TagLetter.c ∈ word :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨left, right, word_eq⟩ := List.mem_iff_append.mp c_mem
  subst word
  have counts : left.count .c + (right.count .c + 1) = 1 := by
    simpa [List.count_append] using count_one
  have left_zero : left.count .c = 0 := by omega
  have right_zero : right.count .c = 0 := by omega
  refine ⟨left.length, right.length, ?_⟩
  rw [eq_bRun_of_count_c_zero left left_zero,
    eq_bRun_of_count_c_zero right right_zero]
  simp [sparseBody, bRun]

/-- Every coupled restricted width-three queue whose body contains at most one `c` halts. -/
theorem coupled_halts_of_count_c_le_one (body : List TagLetter)
    (count_le : body.count .c ≤ 1) :
    TagHaltsFrom 3 (tagOutput body) (body.drop 2 ++ [.b]) := by
  by_cases count_zero : body.count .c = 0
  · have body_eq := eq_bRun_of_count_c_zero body count_zero
    rw [body_eq]
    have initial_eq : (bRun body.length).drop 2 ++ [.b] = bRun (body.length - 2 + 1) := by
      rw [bRun, List.drop_replicate, bRun_snoc]
      rfl
    rw [initial_eq]
    exact bRun_halts (bRun body.length) (body.length - 2 + 1)
  · have count_one : body.count .c = 1 := by omega
    obtain ⟨left, right, rfl⟩ := eq_sparseBody_of_count_c_one body count_one
    exact sparseBody_coupled_halts left right

private theorem exists_code_not_halting :
    ∃ code : Nat.Partrec.Code, ¬Undecidability.CodeHalts code := by
  by_contra all_halt_not
  have all_halt : ∀ code : Nat.Partrec.Code, Undecidability.CodeHalts code :=
    not_exists_not.mp all_halt_not
  apply Undecidability.codeHalts_not_computable
  let decideAll : DecidablePred Undecidability.CodeHalts :=
    fun code => isTrue (all_halt code)
  refine ⟨decideAll, ?_⟩
  have constant : Computable (fun _ : Nat.Partrec.Code => true) :=
    Computable.const true
  change Computable (fun _ : Nat.Partrec.Code => true)
  exact constant

/-- Any exact source family for code halting must leave the sparse-body stratum. -/
theorem exact_source_has_body_with_two_c (body : Nat.Partrec.Code → List TagLetter)
    (exact : ∀ code,
      TagHaltsFrom 3 (tagOutput (body code)) ((body code).drop 2 ++ [.b]) ↔
        Undecidability.CodeHalts code) :
    ∃ code, 2 ≤ (body code).count .c := by
  obtain ⟨code, code_diverges⟩ := exists_code_not_halting
  refine ⟨code, ?_⟩
  by_contra count_not_two
  have count_le : (body code).count .c ≤ 1 := by omega
  exact code_diverges <| (exact code).mp <|
    coupled_halts_of_count_c_le_one (body code) count_le

end WidthThreeSparseBody
end MatrixMortality
