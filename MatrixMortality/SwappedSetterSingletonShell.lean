import MatrixMortality.SwappedSetterMultitransfer
import MatrixMortality.SwappedSetterFringeLanguage

/-!
# Distinguished-boundary singleton shell

The swapped setter's one-transfer branch has two coefficient depths.  The depth-one branch is
handled by `SwappedSetterPositiveDepthOne`; this file closes the depth-`β` branch, whose target
is one of the two singleton erasures.
-/

namespace MatrixMortality.SwappedSetterSingletonShell

open SwappedSetterMultitransfer
open SwappedSetterFringe

private theorem swappedCode_append (left right : List Bool) :
    swappedCode (left ++ right) = 3 ^ right.length * swappedCode left + swappedCode right := by
  simp only [swappedCode, List.map_append, ternaryCode_append, List.length_map]

private theorem swappedCode_lt_pow_length (word : List Bool) :
    swappedCode word < 3 ^ word.length := by
  simpa [swappedCode] using ternaryCode_lt_pow_length (word.map Bool.not)

private theorem swappedCode_lower_bound (word : List Bool) (word_nonempty : word ≠ []) :
    3 ^ (word.length - 1) ≤ swappedCode word := by
  have mapped_nonempty : word.map Bool.not ≠ [] := by
    simpa using word_nonempty
  simpa [swappedCode] using ternaryCode_lower_bound (word.map Bool.not) mapped_nonempty

private theorem eq_pair_of_length_two {word : List Bool} (length_eq : word.length = 2) :
    ∃ first second, word = [first, second] := by
  cases word with
  | nil => simp at length_eq
  | cons first tail =>
      cases tail with
      | nil => simp at length_eq
      | cons second rest =>
          have rest_empty : rest = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at length_eq
            omega
          subst rest
          exact ⟨first, second, rfl⟩

private theorem addTwoPair_classify
    (upperFirst upperSecond lowerFirst lowerSecond : Bool)
    {upperFrontCode lowerFrontCode : Nat}
    (equation :
      9 * upperFrontCode + swappedCode [upperFirst, upperSecond] + 2 =
        9 * lowerFrontCode + swappedCode [lowerFirst, lowerSecond]) :
    upperFirst = true ∧ upperSecond = false ∧
      lowerFirst = false ∧ lowerSecond = true ∧
        upperFrontCode = lowerFrontCode := by
  cases upperFirst <;> cases upperSecond <;> cases lowerFirst <;> cases lowerSecond <;>
    norm_num [swappedCode, ternaryCode, ternaryDigit, Nat.ofDigits] at equation ⊢ <;>
    omega

private theorem addFourPair_classify
    (upperFirst upperSecond lowerFirst lowerSecond : Bool)
    {upperFrontCode lowerFrontCode : Nat}
    (equation :
      9 * upperFrontCode + swappedCode [upperFirst, upperSecond] =
        9 * lowerFrontCode + swappedCode [lowerFirst, lowerSecond] + 4) :
    upperFirst = false ∧ upperSecond = false ∧
      lowerFirst = true ∧ lowerSecond = true ∧
        upperFrontCode = lowerFrontCode := by
  cases upperFirst <;> cases upperSecond <;> cases lowerFirst <;> cases lowerSecond <;>
    norm_num [swappedCode, ternaryCode, ternaryDigit, Nat.ofDigits] at equation ⊢ <;>
    omega

private theorem swappedCode_add_two_pair
    {frontLength : Nat} {upper lower : List Bool}
    (upper_length : upper.length = frontLength + 2)
    (lower_length : lower.length = frontLength + 2)
    (code_eq : swappedCode upper + 2 = swappedCode lower) :
    ∃ front,
      front.length = frontLength ∧
        upper = front ++ [true, false] ∧ lower = front ++ [false, true] := by
  let upperFront := upper.take frontLength
  let lowerFront := lower.take frontLength
  let upperTail := upper.drop frontLength
  let lowerTail := lower.drop frontLength
  have upper_eq : upper = upperFront ++ upperTail :=
    (List.take_append_drop frontLength upper).symm
  have lower_eq : lower = lowerFront ++ lowerTail :=
    (List.take_append_drop frontLength lower).symm
  have upperFront_length : upperFront.length = frontLength := by
    dsimp [upperFront]
    rw [List.length_take, Nat.min_eq_left]
    omega
  have lowerFront_length : lowerFront.length = frontLength := by
    dsimp [lowerFront]
    rw [List.length_take, Nat.min_eq_left]
    omega
  have upperTail_length : upperTail.length = 2 := by
    dsimp [upperTail]
    rw [List.length_drop, upper_length]
    omega
  have lowerTail_length : lowerTail.length = 2 := by
    dsimp [lowerTail]
    rw [List.length_drop, lower_length]
    omega
  obtain ⟨upperFirst, upperSecond, upperTail_eq⟩ :=
    eq_pair_of_length_two upperTail_length
  obtain ⟨lowerFirst, lowerSecond, lowerTail_eq⟩ :=
    eq_pair_of_length_two lowerTail_length
  rw [upper_eq, lower_eq, upperTail_eq, lowerTail_eq,
    swappedCode_append, swappedCode_append] at code_eq
  rw [upperTail_eq] at upper_eq
  rw [lowerTail_eq] at lower_eq
  norm_num only [List.length_cons, List.length_nil, Nat.reduceAdd, pow_two] at code_eq
  obtain ⟨rfl, rfl, rfl, rfl, front_code_eq⟩ :=
    addTwoPair_classify upperFirst upperSecond lowerFirst lowerSecond code_eq
  have front_eq : upperFront = lowerFront := by
    apply swappedTernaryCode_injective
    simpa [swappedCode] using front_code_eq
  rw [← front_eq] at lower_eq
  refine ⟨upperFront, upperFront_length, ?_, ?_⟩
  · exact upper_eq
  · exact lower_eq

private theorem swappedCode_add_four_pair
    {frontLength : Nat} {upper lower : List Bool}
    (upper_length : upper.length = frontLength + 2)
    (lower_length : lower.length = frontLength + 2)
    (code_eq : swappedCode upper = swappedCode lower + 4) :
    ∃ front,
      front.length = frontLength ∧
        upper = front ++ [false, false] ∧ lower = front ++ [true, true] := by
  let upperFront := upper.take frontLength
  let lowerFront := lower.take frontLength
  let upperTail := upper.drop frontLength
  let lowerTail := lower.drop frontLength
  have upper_eq : upper = upperFront ++ upperTail :=
    (List.take_append_drop frontLength upper).symm
  have lower_eq : lower = lowerFront ++ lowerTail :=
    (List.take_append_drop frontLength lower).symm
  have upperFront_length : upperFront.length = frontLength := by
    dsimp [upperFront]
    rw [List.length_take, Nat.min_eq_left]
    omega
  have upperTail_length : upperTail.length = 2 := by
    dsimp [upperTail]
    rw [List.length_drop, upper_length]
    omega
  have lowerTail_length : lowerTail.length = 2 := by
    dsimp [lowerTail]
    rw [List.length_drop, lower_length]
    omega
  obtain ⟨upperFirst, upperSecond, upperTail_eq⟩ :=
    eq_pair_of_length_two upperTail_length
  obtain ⟨lowerFirst, lowerSecond, lowerTail_eq⟩ :=
    eq_pair_of_length_two lowerTail_length
  rw [upper_eq, lower_eq, upperTail_eq, lowerTail_eq,
    swappedCode_append, swappedCode_append] at code_eq
  rw [upperTail_eq] at upper_eq
  rw [lowerTail_eq] at lower_eq
  norm_num only [List.length_cons, List.length_nil, Nat.reduceAdd, pow_two] at code_eq
  obtain ⟨rfl, rfl, rfl, rfl, front_code_eq⟩ :=
    addFourPair_classify upperFirst upperSecond lowerFirst lowerSecond code_eq
  have front_eq : upperFront = lowerFront := by
    apply swappedTernaryCode_injective
    simpa [swappedCode] using front_code_eq
  rw [← front_eq] at lower_eq
  refine ⟨upperFront, upperFront_length, ?_, ?_⟩
  · exact upper_eq
  · exact lower_eq

/-- The unique nonzero-ternary carry pattern with discrepancy `4·3^β-2`. -/
theorem twoMarkerDiscrepancy_pattern
    {β : Nat} (β_large : 3 ≤ β) {upper lower : List Bool}
    (upper_length : upper.length = 2 * β + 1)
    (lower_length : lower.length = 2 * β + 1)
    (code_eq : swappedCode upper = swappedCode lower + (4 * 3 ^ β - 2)) :
    ∃ common middle,
      common.length = β - 1 ∧
        middle.length = β - 2 ∧
          upper = common ++ [false, false] ++ middle ++ [true, false] ∧
          lower = common ++ [true, true] ++ middle ++ [false, true] := by
  let upperFront := upper.take (β + 1)
  let lowerFront := lower.take (β + 1)
  let upperTail := upper.drop (β + 1)
  let lowerTail := lower.drop (β + 1)
  have upper_eq : upper = upperFront ++ upperTail :=
    (List.take_append_drop (β + 1) upper).symm
  have lower_eq : lower = lowerFront ++ lowerTail :=
    (List.take_append_drop (β + 1) lower).symm
  have upperFront_length : upperFront.length = β + 1 := by
    dsimp [upperFront]
    rw [List.length_take, Nat.min_eq_left]
    omega
  have lowerFront_length : lowerFront.length = β + 1 := by
    dsimp [lowerFront]
    rw [List.length_take, Nat.min_eq_left]
    omega
  have upperTail_length : upperTail.length = β := by
    dsimp [upperTail]
    rw [List.length_drop, upper_length]
    omega
  have lowerTail_length : lowerTail.length = β := by
    dsimp [lowerTail]
    rw [List.length_drop, lower_length]
    omega
  have scale_pos : 0 < 3 ^ β := pow_pos (by omega) β
  have upperTail_lt : swappedCode upperTail < 3 ^ β := by
    simpa [upperTail_length] using swappedCode_lt_pow_length upperTail
  have lowerTail_lt : swappedCode lowerTail < 3 ^ β := by
    simpa [lowerTail_length] using swappedCode_lt_pow_length lowerTail
  have lowerTail_ne : lowerTail ≠ [] := by
    intro tail_empty
    have length_zero := congrArg List.length tail_empty
    simp only [List.length_nil] at length_zero
    omega
  have lowerTail_bound : 3 ≤ swappedCode lowerTail := by
    have raw := swappedCode_lower_bound lowerTail lowerTail_ne
    rw [lowerTail_length] at raw
    have exponent_pos : 1 ≤ β - 1 := by omega
    have power_mono : 3 ^ 1 ≤ 3 ^ (β - 1) :=
      Nat.pow_le_pow_right (by omega) exponent_pos
    omega
  have code_eq_add : swappedCode upper + 2 = swappedCode lower + 4 * 3 ^ β := by
    have two_le : 2 ≤ 4 * 3 ^ β := by omega
    omega
  have tail_modEq :
      swappedCode upperTail + 2 ≡ swappedCode lowerTail [MOD 3 ^ β] := by
    have expanded := code_eq_add
    rw [upper_eq, lower_eq, swappedCode_append, swappedCode_append,
      upperTail_length, lowerTail_length] at expanded
    have congruence := congrArg (fun value : Nat => value % 3 ^ β) expanded
    rw [Nat.ModEq]
    simpa [Nat.add_mod] using congruence
  have tail_code_eq : swappedCode upperTail + 2 = swappedCode lowerTail := by
    by_contra code_ne
    have scale_le : 3 ^ β ≤ swappedCode upperTail + 2 := by
      by_contra sum_lt
      have sum_lt' : swappedCode upperTail + 2 < 3 ^ β := Nat.lt_of_not_ge sum_lt
      exact code_ne <| tail_modEq.eq_of_lt_of_lt sum_lt' lowerTail_lt
    have sum_lt_twice : swappedCode upperTail + 2 < 2 * 3 ^ β := by
      omega
    have reduced_lt : swappedCode upperTail + 2 - 3 ^ β < 3 ^ β := by omega
    have reduced_eq :
        swappedCode upperTail + 2 - 3 ^ β = swappedCode lowerTail := by
      rw [Nat.ModEq] at tail_modEq
      rw [Nat.mod_eq_sub_mod scale_le, Nat.mod_eq_of_lt reduced_lt,
        Nat.mod_eq_of_lt lowerTail_lt] at tail_modEq
      exact tail_modEq
    omega
  obtain ⟨middle, middle_length, upperTail_eq, lowerTail_eq⟩ :=
    swappedCode_add_two_pair (frontLength := β - 2)
      (by omega) (by omega) tail_code_eq
  rw [upperTail_eq, lowerTail_eq] at tail_code_eq
  have front_code_eq : swappedCode upperFront = swappedCode lowerFront + 4 := by
    have expanded := code_eq_add
    rw [upper_eq, lower_eq, swappedCode_append, swappedCode_append,
      upperTail_length, lowerTail_length, upperTail_eq, lowerTail_eq] at expanded
    have tail_pair_code :
        swappedCode (middle ++ [true, false]) + 2 =
          swappedCode (middle ++ [false, true]) := by
      exact tail_code_eq
    have scaled :
        3 ^ β * swappedCode upperFront =
          3 ^ β * (swappedCode lowerFront + 4) := by
      rw [Nat.mul_add]
      omega
    exact Nat.eq_of_mul_eq_mul_left scale_pos scaled
  obtain ⟨common, common_length, upperFront_eq, lowerFront_eq⟩ :=
    swappedCode_add_four_pair (frontLength := β - 1)
      (by omega) (by omega) front_code_eq
  refine ⟨common, middle, common_length, middle_length, ?_, ?_⟩
  · rw [upper_eq, upperFront_eq, upperTail_eq]
    simp only [List.append_assoc]
  · rw [lower_eq, lowerFront_eq, lowerTail_eq]
    simp only [List.append_assoc]

private def upperStream (β : Nat) (letters : List TagLetter) : List Bool :=
  tagEncode β letters ++ nearyMarker β

private theorem upperStream_nil {β : Nat} (β_pos : 0 < β) :
    upperStream β [] = true :: false :: List.replicate (β - 1) false := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  simp [upperStream, nearyMarker, List.replicate_succ]

private theorem upperStream_b {β : Nat} (β_pos : 0 < β) (letters : List TagLetter) :
    upperStream β (.b :: letters) =
      true :: false ::
        (List.replicate (β - 1) false ++ true :: upperStream β letters) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  simp [upperStream, tagEncode_cons, tagCode, List.replicate_succ,
    List.append_assoc]

private theorem upperStream_c (β : Nat) (letters : List TagLetter) :
    upperStream β (.c :: letters) = true :: upperStream β letters := by
  simp [upperStream, tagEncode_cons, tagCode]

private theorem firstB_or_allC (letters : List TagLetter) :
    (∃ count tail, letters = List.replicate count .c ++ .b :: tail) ∨
      ∃ count, letters = List.replicate count .c := by
  induction letters with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons letter letters induction =>
      cases letter with
      | b => exact Or.inl ⟨0, letters, rfl⟩
      | c =>
          rcases induction with ⟨count, tail, letters_eq⟩ | ⟨count, letters_eq⟩
          · left
            refine ⟨count + 1, tail, ?_⟩
            simp [letters_eq, List.replicate_succ]
          · right
            exact ⟨count + 1, by rw [letters_eq, List.replicate_succ]⟩

private theorem tagEncode_replicate_c (β count : Nat) :
    tagEncode β (List.replicate count .c) = List.replicate count true := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, tagEncode_cons, tagCode]
      exact congrArg (fun bits => true :: bits) induction

private theorem replicate_append_cons {α : Type*} (value : α) (count : Nat)
    (tail : List α) :
    List.replicate count value ++ value :: tail =
      List.replicate (count + 1) value ++ tail := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ']

private theorem tagEncode_firstB
    (β count : Nat) (tail : List TagLetter) :
    tagEncode β (List.replicate count .c ++ .b :: tail) =
      List.replicate (count + 1) true ++
        List.replicate β false ++ true :: tagEncode β tail := by
  rw [tagEncode_append, tagEncode_replicate_c]
  simp only [tagEncode_cons, tagCode, List.singleton_append]
  calc
    List.replicate count true ++
          (true :: List.replicate β false ++ [true] ++ tagEncode β tail) =
        List.replicate count true ++
          (true :: (List.replicate β false ++ true :: tagEncode β tail)) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    _ =
        List.replicate (count + 1) true ++
          (List.replicate β false ++ true :: tagEncode β tail) :=
      replicate_append_cons true count _
    _ = List.replicate (count + 1) true ++
          List.replicate β false ++ true :: tagEncode β tail :=
      (List.append_assoc _ _ _).symm

private theorem upperStream_firstB
    (β count : Nat) (tail : List TagLetter) :
    upperStream β (List.replicate count .c ++ .b :: tail) =
      List.replicate (count + 1) true ++
        List.replicate β false ++ true :: upperStream β tail := by
  rw [upperStream, tagEncode_append, tagEncode_replicate_c]
  simp only [tagEncode_cons, tagCode, List.singleton_append]
  have tail_eq :
      (true :: List.replicate β false ++ [true] ++ tagEncode β tail) ++ nearyMarker β =
        true :: List.replicate β false ++ true :: upperStream β tail := by
    simp [upperStream, List.append_assoc]
  rw [List.append_assoc]
  rw [tail_eq]
  calc
    List.replicate count true ++
          (true :: List.replicate β false ++ true :: upperStream β tail) =
        List.replicate (count + 1) true ++
          (List.replicate β false ++ true :: upperStream β tail) :=
      replicate_append_cons true count _
    _ = List.replicate (count + 1) true ++
          List.replicate β false ++ true :: upperStream β tail :=
      (List.append_assoc _ _ _).symm

private theorem upperStream_allC
    (β count : Nat) :
    upperStream β (List.replicate count .c) =
      List.replicate (count + 1) true ++ List.replicate β false := by
  rw [upperStream, tagEncode_replicate_c]
  change
    List.replicate count true ++ true :: List.replicate β false = _
  exact replicate_append_cons true count _

private theorem initialOnes_le_of_false
    {initialOnes : Nat} {rest front suffix : List Bool}
    (stream_eq : List.replicate initialOnes true ++ rest = front ++ false :: suffix) :
    initialOnes ≤ front.length := by
  have value : (List.replicate initialOnes true ++ rest)[front.length]? = some false := by
    rw [stream_eq]
    simp
  by_contra initial_not_le
  have inside : front.length < initialOnes := Nat.lt_of_not_ge initial_not_le
  rw [List.getElem?_append_left (by simpa using inside),
    List.getElem?_replicate_of_lt inside] at value
  simp at value

private theorem shortPrefix_zero_starts_at_end
    {β initialOnes : Nat} {front rest suffix : List Bool}
    (initial_pos : 0 < initialOnes)
    (prefix_short : front.length + 2 ≤ β - 1)
    (stream_eq :
      List.replicate initialOnes true ++ (List.replicate β false ++ rest) =
        front ++ [true, false] ++ suffix) :
    initialOnes = front.length + 1 := by
  have penultimate_value :
      (List.replicate initialOnes true ++
          (List.replicate β false ++ rest))[front.length]? = some true := by
    rw [stream_eq]
    simp
  have last_value :
      (List.replicate initialOnes true ++
          (List.replicate β false ++ rest))[front.length + 1]? = some false := by
    rw [stream_eq]
    simp
  by_contra initial_ne
  rcases lt_or_gt_of_ne initial_ne with initial_lt | initial_gt
  · have penultimate_after : initialOnes ≤ front.length := by omega
    have penultimate_inside : front.length - initialOnes < β := by omega
    rw [List.getElem?_append_right (by simpa using penultimate_after)] at penultimate_value
    simp only [List.length_replicate] at penultimate_value
    rw [List.getElem?_append_left (by simpa using penultimate_inside),
      List.getElem?_replicate_of_lt penultimate_inside] at penultimate_value
    simp at penultimate_value
  · have last_before : front.length + 1 < initialOnes := by omega
    rw [List.getElem?_append_left (by simpa using last_before),
      List.getElem?_replicate_of_lt last_before] at last_value
    simp at last_value

private theorem upperStream_starts_true (β : Nat) (letters : List TagLetter) :
    ∃ tail, upperStream β letters = true :: tail := by
  cases letters with
  | nil => exact ⟨List.replicate β false, by simp [upperStream, nearyMarker]⟩
  | cons letter letters =>
      cases letter with
      | b =>
          exact ⟨List.replicate β false ++ true :: upperStream β letters,
            by simp [upperStream, tagEncode_cons, tagCode, List.append_assoc]⟩
      | c => exact ⟨upperStream β letters, upperStream_c β letters⟩

/-- Upper prefix forced by the singleton-shell carry at first-`b` position `count`. -/
def betaUpperPattern (β count : Nat) : List Bool :=
  List.replicate (count + 1) true ++
    List.replicate β false ++
      List.replicate (β - count - 2) true ++ [true, false]

/-- Corresponding lower prefix forced by the same carry. -/
def betaLowerPattern (β count : Nat) : List Bool :=
  List.replicate (count + 1) true ++
    List.replicate (β - count - 2) false ++ [true, true] ++
      List.replicate count false ++
        List.replicate (β - count - 2) true ++ [false, true]

private def betaLowerTailPattern (β count : Nat) : List Bool :=
  List.replicate count true ++
    List.replicate (β - count - 2) false ++ [true, true] ++
      List.replicate count false ++
        List.replicate (β - count - 2) true ++ [false, true]

private theorem betaLowerPattern_cons (β count : Nat) :
    betaLowerPattern β count = true :: betaLowerTailPattern β count := by
  simp [betaLowerPattern, betaLowerTailPattern, List.replicate_succ,
    List.append_assoc]

private theorem betaUpperPattern_length
    {β count : Nat} (β_large : 3 ≤ β) (count_bound : count ≤ β - 3) :
    (betaUpperPattern β count).length = 2 * β + 1 := by
  simp only [betaUpperPattern, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

private theorem betaLowerPattern_length
    {β count : Nat} (β_large : 3 ≤ β) (count_bound : count ≤ β - 3) :
    (betaLowerPattern β count).length = 2 * β + 1 := by
  simp only [betaLowerPattern, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

private theorem betaLowerTail_not_prefix_tagEncode
    {β count : Nat} (β_large : 3 ≤ β) (count_pos : 0 < count)
    (count_bound : count ≤ β - 3) {body : List TagLetter} {suffix : List Bool}
    (body_long : β - 1 ≤ body.length) :
    ¬betaLowerTailPattern β count <+:
      tagEncode β body ++ [true, false] ++ suffix := by
  intro isPrefix
  obtain ⟨residual, prefix_eq⟩ := isPrefix
  let zeroCount := β - count - 2
  have zeroCount_pos : 0 < zeroCount := by
    dsimp [zeroCount]
    omega
  obtain ⟨zeroTail, zeroCount_eq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt zeroCount_pos)
  have target_false_form :
      betaLowerTailPattern β count =
        List.replicate count true ++ false ::
          (List.replicate zeroTail false ++ [true, true] ++
            List.replicate count false ++
              List.replicate (β - count - 2) true ++ [false, true]) := by
    simp [betaLowerTailPattern, zeroCount, zeroCount_eq, List.replicate_succ,
      List.append_assoc]
  let targetFront :=
    List.replicate count true ++ List.replicate (β - count - 2) false
  have targetFront_length : targetFront.length = β - 2 := by
    dsimp [targetFront]
    simp only [List.length_append, List.length_replicate]
    omega
  have target_true_form :
      betaLowerTailPattern β count =
        targetFront ++ true ::
          (true :: List.replicate count false ++
            List.replicate (β - count - 2) true ++ [false, true]) := by
    simp [betaLowerTailPattern, targetFront, List.append_assoc]
  rcases firstB_or_allC body with
      ⟨firstB, tail, body_eq⟩ | ⟨allC, body_eq⟩
  · have physical_false_form :
        List.replicate (firstB + 1) true ++
            (List.replicate β false ++
              true :: (tagEncode β tail ++ [true, false] ++ suffix)) =
          List.replicate count true ++ false ::
            ((List.replicate zeroTail false ++ [true, true] ++
                List.replicate count false ++
                  List.replicate (β - count - 2) true ++ [false, true]) ++
              residual) := by
      calc
        List.replicate (firstB + 1) true ++
              (List.replicate β false ++
                true :: (tagEncode β tail ++ [true, false] ++ suffix)) =
            (tagEncode β body ++ [true, false] ++ suffix) := by
          rw [body_eq, tagEncode_firstB]
          simp only [List.append_assoc, List.cons_append]
        _ = betaLowerTailPattern β count ++ residual := prefix_eq.symm
        _ = List.replicate count true ++ false ::
              ((List.replicate zeroTail false ++ [true, true] ++
                  List.replicate count false ++
                    List.replicate (β - count - 2) true ++ [false, true]) ++
                residual) := by
          rw [target_false_form]
          simp only [List.append_assoc, List.cons_append]
    have firstB_bound : firstB + 1 ≤ count :=
      by simpa using initialOnes_le_of_false physical_false_form
    have physical_true_form :
        List.replicate (firstB + 1) true ++
            (List.replicate β false ++
              true :: (tagEncode β tail ++ [true, false] ++ suffix)) =
          targetFront ++ true ::
            ((true :: List.replicate count false ++
                List.replicate (β - count - 2) true ++ [false, true]) ++ residual) := by
      calc
        List.replicate (firstB + 1) true ++
              (List.replicate β false ++
                true :: (tagEncode β tail ++ [true, false] ++ suffix)) =
            tagEncode β body ++ [true, false] ++ suffix := by
          rw [body_eq, tagEncode_firstB]
          simp only [List.append_assoc, List.cons_append]
        _ = betaLowerTailPattern β count ++ residual := prefix_eq.symm
        _ = targetFront ++ true ::
              ((true :: List.replicate count false ++
                  List.replicate (β - count - 2) true ++ [false, true]) ++ residual) := by
          rw [target_true_form]
          simp only [List.append_assoc, List.cons_append]
    have physical_value :
        (List.replicate (firstB + 1) true ++
          (List.replicate β false ++
            true :: (tagEncode β tail ++ [true, false] ++ suffix)))[β - 2]? =
          some false := by
      have after_initial : firstB + 1 ≤ β - 2 := by omega
      have inside_zeroes : β - 2 - (firstB + 1) < β := by omega
      rw [List.getElem?_append_right (by simpa using after_initial)]
      simp only [List.length_replicate]
      rw [List.getElem?_append_left (by simpa using inside_zeroes),
        List.getElem?_replicate_of_lt inside_zeroes]
    have target_value :
        (List.replicate (firstB + 1) true ++
          (List.replicate β false ++
            true :: (tagEncode β tail ++ [true, false] ++ suffix)))[β - 2]? =
          some true := by
      rw [physical_true_form]
      rw [List.getElem?_append_right (by rw [targetFront_length])]
      rw [targetFront_length, Nat.sub_self]
      rfl
    rw [physical_value] at target_value
    simp at target_value
  · have body_length : body.length = allC := by
      rw [body_eq]
      simp
    have physical_form :
        tagEncode β body ++ [true, false] ++ suffix =
          List.replicate (allC + 1) true ++ false :: suffix := by
      rw [body_eq, tagEncode_replicate_c]
      simpa only [List.append_assoc, List.cons_append, List.singleton_append,
        List.nil_append] using
        replicate_append_cons true allC (false :: suffix)
    have false_form :
        List.replicate (allC + 1) true ++ false :: suffix =
          List.replicate count true ++ false ::
            ((List.replicate zeroTail false ++ [true, true] ++
                List.replicate count false ++
                  List.replicate (β - count - 2) true ++ [false, true]) ++ residual) := by
      calc
        List.replicate (allC + 1) true ++ false :: suffix =
            tagEncode β body ++ [true, false] ++ suffix := physical_form.symm
        _ = betaLowerTailPattern β count ++ residual := prefix_eq.symm
        _ = _ := by
          rw [target_false_form]
          simp only [List.append_assoc, List.cons_append]
    have initial_bound : allC + 1 ≤ count := by
      simpa using initialOnes_le_of_false false_form
    omega

private theorem betaLowerPattern_not_prefix_lower
    {β count : Nat} (β_large : 3 ≤ β) (count_bound : count ≤ β - 3)
    {body : List TagLetter} (body_long : β - 1 ≤ body.length)
    {word : List NearyTile} {tail : List TagLetter}
    (letters_eq :
      word.map NearyTile.letter = List.replicate count .c ++ .b :: tail) :
    ¬betaLowerPattern β count <+: spell (nearyLower β body) word := by
  intro isPrefix
  obtain ⟨residual, prefix_eq⟩ := isPrefix
  cases word with
  | nil => simp at letters_eq
  | cons tile rest =>
      by_cases count_zero : count = 0
      · subst count
        simp only [List.map_cons, List.replicate_zero] at letters_eq
        have tile_b : tile.letter = .b := (List.cons.inj letters_eq).1
        cases tile with
        | rule letter =>
            cases letter with
            | c => simp [NearyTile.letter] at tile_b
            | b =>
                obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
                simp [betaLowerPattern, spell, nearyLower, List.replicate_succ,
                  List.append_assoc] at prefix_eq
                have zeroCount_eq : 3 + offset - 2 = offset + 1 := by omega
                rw [zeroCount_eq, List.replicate_succ] at prefix_eq
                simp at prefix_eq
        | erase letter =>
            cases letter with
            | c => simp [NearyTile.letter] at tile_b
            | b =>
                simp [betaLowerPattern, spell, nearyLower,
                  List.replicate_succ] at prefix_eq
      · obtain ⟨prior, count_eq⟩ := Nat.exists_eq_succ_of_ne_zero count_zero
        rw [count_eq, List.replicate_succ] at letters_eq
        simp only [List.map_cons, List.cons_append] at letters_eq
        have tile_c : tile.letter = .c := (List.cons.inj letters_eq).1
        cases tile with
        | rule letter =>
            cases letter with
            | b => simp [NearyTile.letter] at tile_c
            | c =>
                have tail_prefix :
                    betaLowerTailPattern β count <+:
                      tagEncode β body ++ [true, false] ++
                        spell (nearyLower β body) rest := by
                  refine ⟨residual, ?_⟩
                  rw [betaLowerPattern_cons] at prefix_eq
                  simp only [spell, List.cons_append] at prefix_eq
                  exact List.cons.inj prefix_eq |>.2
                exact betaLowerTail_not_prefix_tagEncode β_large
                  (Nat.pos_of_ne_zero count_zero) count_bound body_long tail_prefix
        | erase letter =>
            cases letter with
            | b => simp [NearyTile.letter] at tile_c
            | c =>
                rw [betaLowerPattern_cons] at prefix_eq
                simp [spell, nearyLower] at prefix_eq

private theorem carryPattern_code_eq (common middle : List Bool) :
    swappedCode (common ++ [false, false] ++ middle ++ [true, false]) + 2 =
      swappedCode (common ++ [true, true] ++ middle ++ [false, true]) +
        4 * 3 ^ (middle.length + 2) := by
  rw [show common ++ [false, false] ++ middle ++ [true, false] =
      (common ++ [false, false]) ++ (middle ++ [true, false]) by
        simp only [List.append_assoc],
    show common ++ [true, true] ++ middle ++ [false, true] =
      (common ++ [true, true]) ++ (middle ++ [false, true]) by
        simp only [List.append_assoc],
    swappedCode_append, swappedCode_append, swappedCode_append, swappedCode_append]
  norm_num [swappedCode, ternaryCode, ternaryDigit, Nat.ofDigits]
  ring

private theorem betaPatterns_carry_form
    {β count : Nat} (β_large : 3 ≤ β) (count_bound : count ≤ β - 3) :
    ∃ common middle,
      middle.length = β - 2 ∧
        betaUpperPattern β count =
          common ++ [false, false] ++ middle ++ [true, false] ∧
        betaLowerPattern β count =
          common ++ [true, true] ++ middle ++ [false, true] := by
  let common :=
    List.replicate (count + 1) true ++
      List.replicate (β - count - 2) false
  let middle :=
    List.replicate count false ++
      List.replicate (β - count - 2) true
  have zero_run :
      List.replicate β false =
        List.replicate (β - count - 2) false ++ [false, false] ++
          List.replicate count false := by
    calc
      List.replicate β false =
          List.replicate ((β - count - 2) + 2 + count) false := by
        congr 1
        omega
      _ = List.replicate (β - count - 2) false ++ [false, false] ++
            List.replicate count false := by
        rw [List.replicate_add, List.replicate_add]
        rfl
  refine ⟨common, middle, ?_, ?_, ?_⟩
  · dsimp [middle]
    simp only [List.length_append, List.length_replicate]
    omega
  · rw [betaUpperPattern, zero_run]
    simp only [common, middle, List.append_assoc]
  · simp only [betaLowerPattern, common, middle, List.append_assoc]

private theorem betaPatterns_code_eq
    {β count : Nat} (β_large : 3 ≤ β) (count_bound : count ≤ β - 3) :
    swappedCode (betaUpperPattern β count) =
      swappedCode (betaLowerPattern β count) + (4 * 3 ^ β - 2) := by
  obtain ⟨common, middle, middle_length, upper_eq, lower_eq⟩ :=
    betaPatterns_carry_form β_large count_bound
  have carry := carryPattern_code_eq common middle
  rw [← upper_eq, ← lower_eq, middle_length] at carry
  have exponent_eq : β - 2 + 2 = β := by omega
  rw [exponent_eq] at carry
  have gap_large : 2 ≤ 4 * 3 ^ β := by
    have power_pos : 0 < 3 ^ β := pow_pos (by omega) β
    omega
  omega

private theorem betaPattern_upperStream
    {β : Nat} (β_large : 3 ≤ β) {letters : List TagLetter}
    {common middle suffix : List Bool}
    (common_length : common.length = β - 1)
    (middle_length : middle.length = β - 2)
    (stream_eq :
      upperStream β letters =
        common ++ [false, false] ++ middle ++ [true, false] ++ suffix) :
    ∃ count tail,
      count ≤ β - 3 ∧
        letters = List.replicate count .c ++ .b :: tail ∧
          betaUpperPattern β count <+: upperStream β letters := by
  rcases firstB_or_allC letters with ⟨count, tail, letters_eq⟩ | ⟨count, letters_eq⟩
  · rw [letters_eq, upperStream_firstB] at stream_eq
    have false_eq :
        List.replicate (count + 1) true ++
            (List.replicate β false ++ true :: upperStream β tail) =
          common ++ false ::
            (false :: middle ++ [true, false] ++ suffix) := by
      simpa only [List.append_assoc, List.cons_append, List.singleton_append,
        List.nil_append] using stream_eq
    have count_bound := initialOnes_le_of_false false_eq
    have count_le : count ≤ β - 2 := by omega
    have count_strict : count ≤ β - 3 := by
      by_contra count_not_le
      have count_eq : count + 1 = β - 1 := by omega
      obtain ⟨tailBits, tail_start⟩ := upperStream_starts_true β tail
      let before := common ++ [false, false] ++ middle
      have before_length : before.length = 2 * β - 1 := by
        dsimp [before]
        simp only [List.length_append, List.length_cons, List.length_nil,
          common_length, middle_length]
        omega
      have last_value :
          (List.replicate (count + 1) true ++
              List.replicate β false ++ true :: upperStream β tail)[before.length + 1]? =
            some false := by
        have stream_eq_before :
            List.replicate (count + 1) true ++
                List.replicate β false ++ true :: upperStream β tail =
              before ++ [true, false] ++ suffix := by
          simpa [before, List.append_assoc] using stream_eq
        rw [stream_eq_before,
          List.getElem?_append_left (by simp),
          List.getElem?_append_right (by simp)]
        simp
      rw [tail_start] at last_value
      have normalized :
          List.replicate (count + 1) true ++
                List.replicate β false ++ true :: true :: tailBits =
            (List.replicate (count + 1) true ++
                List.replicate β false ++ [true]) ++ true :: tailBits := by
        simp only [List.append_assoc, List.singleton_append]
      have head_length :
          (List.replicate (count + 1) true ++
              List.replicate β false ++ [true]).length = before.length + 1 := by
        simp only [List.length_append, List.length_replicate, List.length_singleton,
          before_length]
        omega
      rw [normalized, List.getElem?_append_right (by rw [head_length])] at last_value
      rw [head_length, Nat.sub_self] at last_value
      simp at last_value
    let tailFront :=
      (common ++ [false, false] ++ middle).drop
        ((count + 1) + β + 1)
    have tailFront_length : tailFront.length = β - count - 3 := by
      dsimp [tailFront]
      rw [List.length_drop]
      simp only [List.length_append, List.length_cons, List.length_nil,
        common_length, middle_length]
      omega
    have tail_stream_eq :
        upperStream β tail = tailFront ++ [true, false] ++ suffix := by
      have dropped := congrArg
        (List.drop ((count + 1) + β + 1)) stream_eq
      let head :=
        List.replicate (count + 1) true ++ List.replicate β false ++ [true]
      have head_length : head.length = (count + 1) + β + 1 := by
        dsimp [head]
        simp only [List.length_append, List.length_replicate, List.length_singleton]
      have left_form :
          List.replicate (count + 1) true ++
              List.replicate β false ++ true :: upperStream β tail =
            head ++ upperStream β tail := by
        simp [head, List.append_assoc]
      have right_form :
          common ++ [false, false] ++ middle ++ [true, false] ++ suffix =
            (common ++ [false, false] ++ middle) ++ ([true, false] ++ suffix) := by
        simp [List.append_assoc]
      have head_le :
          (count + 1) + β + 1 ≤ (common ++ [false, false] ++ middle).length := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          common_length, middle_length]
        omega
      rw [left_form, right_form, ← head_length, List.drop_append_length,
        List.drop_append_of_le_length (by simpa [head_length] using head_le)] at dropped
      simpa [tailFront, head_length] using dropped
    rcases firstB_or_allC tail with
        ⟨nextCount, rest, tail_eq⟩ | ⟨nextCount, tail_eq⟩
    · rw [tail_eq, upperStream_firstB] at tail_stream_eq
      have next_eq := shortPrefix_zero_starts_at_end
        (β := β) (initialOnes := nextCount + 1) (front := tailFront)
        (rest := true :: upperStream β rest) (suffix := suffix)
        (initial_pos := by omega)
        (prefix_short := by
          rw [tailFront_length]
          have beta_split : β - 1 = (β - 3) + 2 := by omega
          rw [Nat.sub_sub, beta_split]
          exact Nat.add_le_add_right (Nat.sub_le_sub_left (by omega) β) 2)
        (stream_eq := by
          simpa only [List.append_assoc] using tail_stream_eq)
      have next_count_eq : nextCount = β - count - 3 := by
        rw [tailFront_length] at next_eq
        omega
      have letters_shape :
          letters = List.replicate count .c ++ .b ::
            (List.replicate (β - count - 3) .c ++ .b :: rest) := by
        rw [letters_eq, tail_eq, next_count_eq]
      refine ⟨count, List.replicate (β - count - 3) .c ++ .b :: rest,
        count_strict, letters_shape, ?_⟩
      rw [letters_shape]
      refine ⟨List.replicate (β - 1) false ++ true :: upperStream β rest, ?_⟩
      simp only [betaUpperPattern, upperStream_firstB, List.append_assoc]
      have ones_split : β - count - 2 = (β - count - 3) + 1 := by omega
      have zeros_split : β = (β - 1) + 1 := by omega
      have ones_eq :
          List.replicate (β - count - 2) true =
            true :: List.replicate (β - count - 3) true := by
        calc
          List.replicate (β - count - 2) true =
              List.replicate ((β - count - 3) + 1) true :=
            congrArg (fun length => List.replicate length true) ones_split
          _ = true :: List.replicate (β - count - 3) true :=
            List.replicate_succ
      have zeros_eq :
          List.replicate β false = false :: List.replicate (β - 1) false := by
        calc
          List.replicate β false = List.replicate ((β - 1) + 1) false :=
            congrArg (fun length => List.replicate length false) zeros_split
          _ = false :: List.replicate (β - 1) false :=
            List.replicate_succ
      have next_ones_eq :
          List.replicate ((β - count - 3) + 1) true =
            List.replicate (β - count - 3) true ++ [true] :=
        List.replicate_succ'
      rw [ones_eq, zeros_eq, next_ones_eq]
      simp only [List.cons_append, List.nil_append,
        List.append_assoc]
    · rw [tail_eq, upperStream_allC] at tail_stream_eq
      have next_eq := shortPrefix_zero_starts_at_end
        (β := β) (initialOnes := nextCount + 1) (front := tailFront)
        (rest := []) (suffix := suffix)
        (initial_pos := by omega)
        (prefix_short := by
          rw [tailFront_length]
          have beta_split : β - 1 = (β - 3) + 2 := by omega
          rw [Nat.sub_sub, beta_split]
          exact Nat.add_le_add_right (Nat.sub_le_sub_left (by omega) β) 2)
        (stream_eq := by
          simpa only [List.append_assoc, List.append_nil] using tail_stream_eq)
      have next_count_eq : nextCount = β - count - 3 := by
        rw [tailFront_length] at next_eq
        omega
      have letters_shape :
          letters = List.replicate count .c ++ .b ::
            List.replicate (β - count - 3) .c := by
        rw [letters_eq, tail_eq, next_count_eq]
      refine ⟨count, List.replicate (β - count - 3) .c,
        count_strict, letters_shape, ?_⟩
      rw [letters_shape]
      refine ⟨List.replicate (β - 1) false, ?_⟩
      simp only [betaUpperPattern, upperStream_firstB, upperStream_allC,
        List.append_assoc]
      have ones_split : β - count - 2 = (β - count - 3) + 1 := by omega
      have zeros_split : β = (β - 1) + 1 := by omega
      have ones_eq :
          List.replicate (β - count - 2) true =
            true :: List.replicate (β - count - 3) true := by
        calc
          List.replicate (β - count - 2) true =
              List.replicate ((β - count - 3) + 1) true :=
            congrArg (fun length => List.replicate length true) ones_split
          _ = true :: List.replicate (β - count - 3) true :=
            List.replicate_succ
      have zeros_eq :
          List.replicate β false = false :: List.replicate (β - 1) false := by
        calc
          List.replicate β false = List.replicate ((β - 1) + 1) false :=
            congrArg (fun length => List.replicate length false) zeros_split
          _ = false :: List.replicate (β - 1) false :=
            List.replicate_succ
      have next_ones_eq :
          List.replicate ((β - count - 3) + 1) true =
            List.replicate (β - count - 3) true ++ [true] :=
        List.replicate_succ'
      rw [ones_eq, zeros_eq, next_ones_eq]
      simp only [List.cons_append, List.nil_append,
        List.append_assoc]
  · rw [letters_eq, upperStream_allC] at stream_eq
    have false_eq :
        List.replicate (count + 1) true ++ List.replicate β false =
          common ++ false ::
            (false :: middle ++ [true, false] ++ suffix) := by
      simpa only [List.append_assoc, List.cons_append, List.singleton_append,
        List.nil_append] using stream_eq
    have count_upper := initialOnes_le_of_false false_eq
    have length_eq := congrArg List.length stream_eq
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, common_length, middle_length] at length_eq
    omega

/-- Exact normalized pole equation in the distinguished-boundary singleton shell. -/
def SingletonShellPole (width : Nat) (discrepancy : ℤ) (target : TagLetter) : Prop :=
  singletonCoefficient width target * discrepancy +
      widthScale width * terminalDiscrepancy width * setterMarker width * 2 = 0

/-- Physical data at a hypothetical distinguished-boundary pole in the depth-`β` singleton
shell. The two length equations record the exact uncancelled shell after common-suffix
cancellation. -/
structure SingletonShellPoleWitness (β : Nat) (body : List TagLetter) where
  /-- Word producing the distinguished-boundary discrepancy. -/
  priorWord : List NearyTile
  /-- Prospective singleton erasure role. -/
  target : TagLetter
  /-- Uncancelled upper prefix. -/
  upperPrefix : List Bool
  /-- Uncancelled lower prefix. -/
  lowerPrefix : List Bool
  /-- Cancelled common suffix. -/
  commonSuffix : List Bool
  /-- Exact upper shell length. -/
  upperLength : upperPrefix.length = 2 * β + 1
  /-- Exact lower shell length. -/
  lowerLength : lowerPrefix.length = 2 * β + 1
  /-- Physical upper factorization before suffix cancellation. -/
  upperFactorization :
    spell (nearyUpper β) priorWord ++ nearyMarker β = upperPrefix ++ commonSuffix
  /-- Physical lower factorization before suffix cancellation. -/
  lowerFactorization :
    spell (nearyLower β body) priorWord = lowerPrefix ++ commonSuffix
  /-- Exact normalized pole equation at the prospective singleton. -/
  exactPole :
    SingletonShellPole β
      ((swappedCode upperPrefix : ℤ) - swappedCode lowerPrefix) target

private theorem widthScale_ge_twentySeven {width : Nat} (width_large : 3 ≤ width) :
    27 ≤ widthScale width := by
  have power_mono : 3 ^ 3 ≤ 3 ^ width := Nat.pow_le_pow_right (by omega) width_large
  change (27 : ℤ) ≤ (3 : ℤ) ^ width
  exact_mod_cast power_mono

/-- A singleton-`b` target would require a nonintegral discrepancy strictly between one and
two. -/
theorem singletonB_pole_false {width : Nat} (width_large : 3 ≤ width)
    (discrepancy : ℤ) (pole : SingletonShellPole width discrepancy .b) : False := by
  let scale := widthScale width
  let marker := setterMarker width
  let terminal := terminalDiscrepancy width
  let cofactor := singletonBCofactor width
  have scale_large : 27 ≤ scale := widthScale_ge_twentySeven width_large
  have scale_pos : 0 < scale := by omega
  have cofactor_pos : 0 < cofactor := by
    dsimp [cofactor, singletonBCofactor]
    nlinarith [sq_nonneg (scale - 2)]
  have numerator_gt : cofactor < 2 * marker * terminal := by
    dsimp [cofactor, marker, terminal, singletonBCofactor, setterMarker,
      terminalDiscrepancy]
    nlinarith [sq_nonneg (scale - 2)]
  have numerator_lt : 2 * marker * terminal < 2 * cofactor := by
    dsimp [cofactor, marker, terminal, singletonBCofactor, setterMarker,
      terminalDiscrepancy]
    nlinarith [sq_nonneg (scale - 2)]
  have pole_reduced : cofactor * discrepancy = 2 * marker * terminal := by
    dsimp [SingletonShellPole, singletonCoefficient] at pole
    change -scale * cofactor * discrepancy + scale * terminal * marker * 2 = 0 at pole
    have scaled : scale * (-(cofactor * discrepancy) + 2 * marker * terminal) = 0 := by
      linear_combination pole
    have inner_zero : -(cofactor * discrepancy) + 2 * marker * terminal = 0 := by
      exact (mul_eq_zero.mp scaled).resolve_left (ne_of_gt scale_pos)
    linarith
  have discrepancy_gt : 1 < discrepancy := by
    nlinarith
  have discrepancy_lt : discrepancy < 2 := by
    nlinarith
  omega

/-- The singleton-`c` pole is equivalent to the unique discrepancy `2μ`. -/
theorem singletonC_pole_iff {width : Nat} (width_large : 3 ≤ width)
    (discrepancy : ℤ) :
    SingletonShellPole width discrepancy .c ↔
      discrepancy = 2 * setterMarker width := by
  have scale_pos : 0 < widthScale width := by
    have scale_large := widthScale_ge_twentySeven width_large
    omega
  have terminal_pos : 0 < terminalDiscrepancy width := by
    dsimp [terminalDiscrepancy]
    have scale_large := widthScale_ge_twentySeven width_large
    omega
  constructor
  · intro pole
    have factored :
        widthScale width * terminalDiscrepancy width *
            (-discrepancy + 2 * setterMarker width) = 0 := by
      dsimp [SingletonShellPole, singletonCoefficient] at pole
      linear_combination pole
    have inner_zero : -discrepancy + 2 * setterMarker width = 0 := by
      exact (mul_eq_zero.mp factored).resolve_left
        (mul_ne_zero (ne_of_gt scale_pos) (ne_of_gt terminal_pos))
    linarith
  · rintro rfl
    simp [SingletonShellPole, singletonCoefficient]
    ring

/-- No physical distinguished-boundary prefix can reach either depth-`β` singleton pole. -/
theorem singletonShellPoleWitness_false
    (envelope : NearyArithmeticEnvelope) (β_large : 3 ≤ envelope.β)
    (witness : SingletonShellPoleWitness envelope.β envelope.body) : False := by
  cases target_eq : witness.target with
  | b =>
      exact singletonB_pole_false β_large _ <| by
        simpa [target_eq] using witness.exactPole
  | c =>
      have pole_c :
          SingletonShellPole envelope.β
            ((swappedCode witness.upperPrefix : ℤ) -
              swappedCode witness.lowerPrefix) .c := by
        simpa [target_eq] using witness.exactPole
      have discrepancy_eq :
          (swappedCode witness.upperPrefix : ℤ) -
              swappedCode witness.lowerPrefix =
            2 * setterMarker envelope.β :=
        (singletonC_pole_iff β_large _).mp pole_c
      have gap_large : 2 ≤ 4 * 3 ^ envelope.β := by
        have power_pos : 0 < 3 ^ envelope.β := pow_pos (by omega) envelope.β
        omega
      have gap_cast :
          ((4 * 3 ^ envelope.β - 2 : Nat) : ℤ) =
            4 * (3 : ℤ) ^ envelope.β - 2 := by
        rw [Nat.cast_sub gap_large]
        norm_num
      have discrepancy_closed :
          (swappedCode witness.upperPrefix : ℤ) -
              swappedCode witness.lowerPrefix =
            4 * (3 : ℤ) ^ envelope.β - 2 := by
        calc
          (swappedCode witness.upperPrefix : ℤ) -
                swappedCode witness.lowerPrefix =
              2 * setterMarker envelope.β := discrepancy_eq
          _ = 4 * (3 : ℤ) ^ envelope.β - 2 := by
            simp [setterMarker, widthScale]
            ring
      have code_eq_int :
          (swappedCode witness.upperPrefix : ℤ) =
            swappedCode witness.lowerPrefix +
              ((4 * 3 ^ envelope.β - 2 : Nat) : ℤ) := by
        rw [gap_cast]
        linarith
      have code_eq :
          swappedCode witness.upperPrefix =
            swappedCode witness.lowerPrefix + (4 * 3 ^ envelope.β - 2) := by
        exact_mod_cast code_eq_int
      obtain ⟨common, middle, common_length, middle_length,
          upper_carry, _lower_carry⟩ :=
        twoMarkerDiscrepancy_pattern β_large witness.upperLength witness.lowerLength code_eq
      have upper_stream :
          upperStream envelope.β (witness.priorWord.map NearyTile.letter) =
            witness.upperPrefix ++ witness.commonSuffix := by
        rw [upperStream, ← spell_nearyUpper]
        exact witness.upperFactorization
      have patterned_stream :
          upperStream envelope.β (witness.priorWord.map NearyTile.letter) =
            common ++ [false, false] ++ middle ++ [true, false] ++
              witness.commonSuffix := by
        rw [upper_stream, upper_carry]
      obtain ⟨count, tail, count_bound, letters_eq, pattern_prefix⟩ :=
        betaPattern_upperStream β_large common_length middle_length patterned_stream
      have upper_prefix :
          witness.upperPrefix <+:
            upperStream envelope.β (witness.priorWord.map NearyTile.letter) :=
        ⟨witness.commonSuffix, upper_stream.symm⟩
      have upper_take := List.prefix_iff_eq_take.mp upper_prefix
      have pattern_take := List.prefix_iff_eq_take.mp pattern_prefix
      have pattern_length := betaUpperPattern_length β_large count_bound
      have equal_lengths :
          (betaUpperPattern envelope.β count).length = witness.upperPrefix.length := by
        rw [pattern_length, witness.upperLength]
      have upper_pattern_eq :
          witness.upperPrefix = betaUpperPattern envelope.β count := by
        calc
          witness.upperPrefix =
              List.take witness.upperPrefix.length
                (upperStream envelope.β
                  (witness.priorWord.map NearyTile.letter)) := upper_take
          _ = List.take (betaUpperPattern envelope.β count).length
                (upperStream envelope.β
                  (witness.priorWord.map NearyTile.letter)) := by
            rw [equal_lengths]
          _ = betaUpperPattern envelope.β count := pattern_take.symm
      have pattern_code_eq := betaPatterns_code_eq β_large count_bound
      rw [← upper_pattern_eq] at pattern_code_eq
      have lower_code_eq :
          swappedCode witness.lowerPrefix =
            swappedCode (betaLowerPattern envelope.β count) := by
        omega
      have lower_pattern_eq :
          witness.lowerPrefix = betaLowerPattern envelope.β count := by
        apply swappedTernaryCode_injective
        simpa [swappedCode] using lower_code_eq
      have lower_prefix :
          betaLowerPattern envelope.β count <+:
            spell (nearyLower envelope.β envelope.body) witness.priorWord := by
        refine ⟨witness.commonSuffix, ?_⟩
        calc
          betaLowerPattern envelope.β count ++ witness.commonSuffix =
              witness.lowerPrefix ++ witness.commonSuffix := by
            rw [lower_pattern_eq]
          _ = spell (nearyLower envelope.β envelope.body) witness.priorWord :=
            witness.lowerFactorization.symm
      exact betaLowerPattern_not_prefix_lower β_large count_bound
        envelope.body_long letters_eq lower_prefix

end MatrixMortality.SwappedSetterSingletonShell
