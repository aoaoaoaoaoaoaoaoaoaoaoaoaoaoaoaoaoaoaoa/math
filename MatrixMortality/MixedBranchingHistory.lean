import MatrixMortality.BranchingRecognizer

/-!
# Equal-length branching in three states

The width-three body `bcbcbb` has complete terminal history language `P₀ (A₀ | B₀)*`, with two
equal-length null blocks. This file proves the grammar and the complete raw-control normal form.
-/

namespace MatrixMortality

namespace MixedBranchingRecognizer

open PeriodicHistory BranchingRecognizer PrefixResidual
open scoped Matrix

/-! ## Exact history grammar -/

/-- The mixed width-three body `bcbcbb`. -/
def mixedBody : List TagLetter := [.b, .c, .b, .c, .b, .b]

/-- The stroke `bcb`. -/
def strokeBCB : Stroke TagLetter 3 := stroke₃ .b .c .b

/-- The fixed three-stroke terminal prefix. -/
def prefixHistory : List (Stroke TagLetter 3) := [strokeCBC, strokeBCB, strokeBBB]

/-- The first equal-length null block `bbb,bcb,cbb`. -/
def nullBlockA : List (Stroke TagLetter 3) := [strokeBBB, strokeBCB, strokeCBB]

/-- The second equal-length null block `bbb,cbc,bbb`. -/
def nullBlockB : List (Stroke TagLetter 3) := [strokeBBB, strokeCBC, strokeBBB]

/-- One binary choice of null block. -/
def nullBlock : Bool → List (Stroke TagLetter 3)
  | false => nullBlockA
  | true => nullBlockB

/-- Concatenation of independently chosen equal-length null blocks. -/
def nullHistory : List Bool → List (Stroke TagLetter 3)
  | [] => []
  | bit :: bits => nullBlock bit ++ nullHistory bits

@[simp] theorem nullHistory_append (left right : List Bool) :
    nullHistory (left ++ right) = nullHistory left ++ nullHistory right := by
  induction left with
  | nil => rfl
  | cons bit bits induction => simp [nullHistory, induction, List.append_assoc]

/-- A null history preserves the one-letter queue. -/
def mixedNull (history : List (Stroke TagLetter 3)) : Prop :=
  consumed history ++ [.b] = [.b] ++ produced (tagOutput mixedBody) history

private abbrev Residual := PrefixResidual.Residual TagLetter

private def startResidual : Residual := .right .b []
private def leftResidual : Residual := .left .b []
private def deepResidual : Residual := .left .b [.c, .b]
private def wideResidual : Residual := .right .b [.b, .b]

private def outputBlock (stroke : Stroke TagLetter 3) : List TagLetter :=
  tagOutput mixedBody stroke.head

private abbrev ResidualStep (before : Residual) (stroke : Stroke TagLetter 3)
    (after : Residual) : Prop :=
  before.leftWord ++ stroke.letters ++ after.rightWord =
    before.rightWord ++ outputBlock stroke ++ after.leftWord

private abbrev ResidualPath (initial : Residual) :
    List (Stroke TagLetter 3) → Residual → Prop :=
  PrefixResidual.Path (tagOutput mixedBody) initial

private theorem mixedNull_iff_path (history : List (Stroke TagLetter 3)) :
    mixedNull history ↔ ResidualPath startResidual history startResidual := by
  constructor
  · intro null
    apply PrefixResidual.path_of_completion (tagOutput mixedBody) .b startResidual [] [.b] history
    · rfl
    · simpa [mixedNull] using null
  · intro path
    have realized := PrefixResidual.Path.realizes path (left := []) (right := [.b]) (by rfl)
    simpa [mixedNull, Residual.Realizes, startResidual, Residual.leftWord,
      Residual.rightWord] using realized

private def rightRigid : Residual → Prop
  | .right head tail =>
      head :: tail = [.b] ∨ head :: tail = [.b, .b] ∨ head :: tail = [.b, .b, .b]
  | .flush | .left _ _ => True

private theorem start_rightRigid : rightRigid startResidual := by
  simp [rightRigid, startResidual]

private theorem rightRigid_step {before after : Residual}
    {stroke : Stroke TagLetter 3} (rigid : rightRigid before)
    (step : ResidualStep before stroke after) : rightRigid after := by
  cases after with
  | flush => trivial
  | left => trivial
  | right afterHead afterTail =>
      rcases stroke with ⟨strokeHead, wake, width⟩
      have wakeLength : wake.length = 2 := by omega
      obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wakeLength
      cases before with
      | flush =>
          cases strokeHead <;> cases wake₁ <;> cases wake₂ <;>
            simp [ResidualStep, Residual.leftWord, Residual.rightWord, outputBlock,
              Stroke.letters, mixedBody, tagOutput, nearyBody] at step ⊢
      | right beforeHead beforeTail =>
          rcases rigid with rigid | rigid | rigid <;>
            simp at rigid <;> rcases rigid with ⟨rfl, rfl⟩ <;>
            cases strokeHead <;> cases wake₁ <;> cases wake₂ <;>
            simp_all [ResidualStep, Residual.leftWord, Residual.rightWord, outputBlock,
              Stroke.letters, mixedBody, tagOutput, nearyBody, rightRigid]
      | left beforeHead beforeTail =>
          cases strokeHead with
          | b =>
              have lengths := congrArg List.length step
              simp [Residual.leftWord, Residual.rightWord, outputBlock,
                Stroke.letters, tagOutput, nearyBody] at lengths
          | c =>
              let prefixPart : List TagLetter :=
                (beforeHead :: beforeTail) ++ [.c, wake₁, wake₂]
              have suffixEquality :
                  prefixPart ++ afterHead :: afterTail =
                    [.b, .c, .b, .c, .b, .b, .b] := by
                simpa [prefixPart, ResidualStep, Residual.leftWord, Residual.rightWord,
                  outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody,
                  List.append_assoc] using step
              have lengths := congrArg List.length suffixEquality
              have afterLength : (afterHead :: afterTail).length ≤ 3 := by
                simp [prefixPart] at lengths
                simp
                omega
              have suffix : afterHead :: afterTail <:+
                  ([.b, .c, .b, .c, .b, .b, .b] : List TagLetter) := by
                exact ⟨prefixPart, suffixEquality⟩
              have suffixFormula := List.suffix_iff_eq_drop.mp suffix
              simp at afterLength
              interval_cases tailLength : afterTail.length
              · obtain rfl := List.length_eq_zero_iff.mp tailLength
                norm_num at suffixFormula
                simpa [rightRigid] using suffixFormula
              · obtain ⟨first, rfl⟩ := List.length_eq_one_iff.mp tailLength
                norm_num at suffixFormula
                simpa [rightRigid] using suffixFormula
              · obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp tailLength
                norm_num at suffixFormula
                simpa [rightRigid] using suffixFormula

private theorem preserves_rightRigid {initial final : Residual}
    {history : List (Stroke TagLetter 3)} (path : ResidualPath initial history final)
    (rigid : rightRigid initial) : rightRigid final := by
  induction path with
  | nil => exact rigid
  | snoc _ step induction => exact rightRigid_step induction step

private theorem enters_start {before : Residual} {stroke : Stroke TagLetter 3}
    (rigid : rightRigid before) (step : ResidualStep before stroke startResidual) :
    (before = deepResidual ∧ stroke = strokeCBB) ∨
      (before = wideResidual ∧ stroke = strokeBBB) := by
  rcases stroke with ⟨head, wake, width⟩
  have wakeLength : wake.length = 2 := by omega
  obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wakeLength
  cases before with
  | flush =>
      cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp [ResidualStep, Residual.leftWord, Residual.rightWord, startResidual,
          outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at step
  | right beforeHead beforeTail =>
      rcases rigid with rigid | rigid | rigid <;>
        simp at rigid <;> rcases rigid with ⟨rfl, rfl⟩ <;>
        cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp_all [ResidualStep, Residual.leftWord, Residual.rightWord, startResidual,
          wideResidual, outputBlock, strokeBBB, stroke₃, Stroke.letters, mixedBody,
          tagOutput, nearyBody]
  | left beforeHead beforeTail =>
      cases head with
      | b =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, startResidual,
            outputBlock, Stroke.letters, tagOutput, nearyBody] at lengths
      | c =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, startResidual,
            outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at lengths
          obtain ⟨tail₁, tail₂, rfl⟩ := List.length_eq_two.mp (by omega : beforeTail.length = 2)
          cases tail₁ <;> cases tail₂ <;> cases wake₁ <;> cases wake₂ <;>
            simp_all [ResidualStep, Residual.leftWord, Residual.rightWord, startResidual,
              deepResidual, outputBlock, strokeCBB, stroke₃, Stroke.letters, mixedBody,
              tagOutput, nearyBody]

private theorem enters_left {before : Residual} {stroke : Stroke TagLetter 3}
    (rigid : rightRigid before) (step : ResidualStep before stroke leftResidual) :
    before = startResidual ∧ stroke = strokeBBB := by
  rcases stroke with ⟨head, wake, width⟩
  have wakeLength : wake.length = 2 := by omega
  obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wakeLength
  cases before with
  | flush =>
      cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp [ResidualStep, Residual.leftWord, Residual.rightWord, leftResidual,
          outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at step
  | right beforeHead beforeTail =>
      rcases rigid with rigid | rigid | rigid <;>
        simp at rigid <;> rcases rigid with ⟨rfl, rfl⟩ <;>
        cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp_all [ResidualStep, Residual.leftWord, Residual.rightWord, startResidual,
          leftResidual, outputBlock, strokeBBB, stroke₃, Stroke.letters, mixedBody,
          tagOutput, nearyBody]
  | left beforeHead beforeTail =>
      cases head with
      | b =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, leftResidual,
            outputBlock, Stroke.letters, tagOutput, nearyBody] at lengths
      | c =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, leftResidual,
            outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at lengths
          have rawEquality :
              (beforeHead :: beforeTail) ++ [.c, wake₁, wake₂] =
                [.b, .c, .b, .c, .b] ++ [.b, .b, .b] := by
            simpa [ResidualStep, Residual.leftWord, Residual.rightWord, leftResidual,
              outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody,
              List.append_assoc] using step
          have beforeLength : (beforeHead :: beforeTail).length =
              ([.b, .c, .b, .c, .b] : List TagLetter).length := by
            simpa using congrArg List.length rawEquality
          have strokeEquality := List.append_inj_right rawEquality beforeLength
          simp at strokeEquality

private theorem enters_deep {before : Residual} {stroke : Stroke TagLetter 3}
    (rigid : rightRigid before) (step : ResidualStep before stroke deepResidual) :
    before = leftResidual ∧ stroke = strokeBCB := by
  rcases stroke with ⟨head, wake, width⟩
  have wakeLength : wake.length = 2 := by omega
  obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wakeLength
  cases before with
  | flush =>
      cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp [ResidualStep, Residual.leftWord, Residual.rightWord, deepResidual,
          outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at step
  | right beforeHead beforeTail =>
      rcases rigid with rigid | rigid | rigid <;>
        simp at rigid <;> rcases rigid with ⟨rfl, rfl⟩ <;>
        cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp_all [ResidualStep, Residual.leftWord, Residual.rightWord,
          deepResidual, outputBlock, Stroke.letters, mixedBody,
          tagOutput, nearyBody]
  | left beforeHead beforeTail =>
      cases head with
      | b =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, deepResidual,
            outputBlock, Stroke.letters, tagOutput, nearyBody] at lengths
          subst beforeTail
          cases beforeHead <;> cases wake₁ <;> cases wake₂ <;>
            simp_all [ResidualStep, Residual.leftWord, Residual.rightWord, leftResidual,
              deepResidual, outputBlock, strokeBCB, stroke₃, Stroke.letters,
              tagOutput, nearyBody]
      | c =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, deepResidual,
            outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at lengths
          have rawEquality :
              (beforeHead :: beforeTail) ++ [.c, wake₁, wake₂] =
                [.b, .c, .b, .c, .b, .b, .b] ++ [.b, .c, .b] := by
            simpa [ResidualStep, Residual.leftWord, Residual.rightWord, deepResidual,
              outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody,
              List.append_assoc] using step
          have beforeLength : (beforeHead :: beforeTail).length =
              ([.b, .c, .b, .c, .b, .b, .b] : List TagLetter).length := by
            simpa using congrArg List.length rawEquality
          have strokeEquality := List.append_inj_right rawEquality beforeLength
          simp at strokeEquality

private theorem enters_wide {before : Residual} {stroke : Stroke TagLetter 3}
    (rigid : rightRigid before) (step : ResidualStep before stroke wideResidual) :
    before = leftResidual ∧ stroke = strokeCBC := by
  rcases stroke with ⟨head, wake, width⟩
  have wakeLength : wake.length = 2 := by omega
  obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wakeLength
  cases before with
  | flush =>
      cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp [ResidualStep, Residual.leftWord, Residual.rightWord, wideResidual,
          outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at step
  | right beforeHead beforeTail =>
      rcases rigid with rigid | rigid | rigid <;>
        simp at rigid <;> rcases rigid with ⟨rfl, rfl⟩ <;>
        cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp_all [ResidualStep, Residual.leftWord, Residual.rightWord,
          wideResidual, outputBlock, Stroke.letters, mixedBody,
          tagOutput, nearyBody]
  | left beforeHead beforeTail =>
      cases head with
      | b =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, wideResidual,
            outputBlock, Stroke.letters, tagOutput, nearyBody] at lengths
      | c =>
          have lengths := congrArg List.length step
          simp [Residual.leftWord, Residual.rightWord, wideResidual,
            outputBlock, Stroke.letters, mixedBody, tagOutput, nearyBody] at lengths
          subst beforeTail
          cases beforeHead <;> cases wake₁ <;> cases wake₂ <;>
            simp_all [ResidualStep, Residual.leftWord, Residual.rightWord, leftResidual,
              wideResidual, outputBlock, strokeCBC, stroke₃, Stroke.letters, mixedBody,
              tagOutput, nearyBody]

private theorem step_start_left :
    ResidualStep startResidual strokeBBB leftResidual := by rfl

private theorem step_left_deep :
    ResidualStep leftResidual strokeBCB deepResidual := by rfl

private theorem step_deep_start :
    ResidualStep deepResidual strokeCBB startResidual := by rfl

private theorem step_left_wide :
    ResidualStep leftResidual strokeCBC wideResidual := by rfl

private theorem step_wide_start :
    ResidualStep wideResidual strokeBBB startResidual := by rfl

private theorem nullBlock_path (bit : Bool) :
    ResidualPath startResidual (nullBlock bit) startResidual := by
  cases bit
  · exact PrefixResidual.Path.cons step_start_left
      (PrefixResidual.Path.cons step_left_deep
        (PrefixResidual.Path.snoc PrefixResidual.Path.nil step_deep_start))
  · exact PrefixResidual.Path.cons step_start_left
      (PrefixResidual.Path.cons step_left_wide
        (PrefixResidual.Path.snoc PrefixResidual.Path.nil step_wide_start))

private theorem nullHistory_path (bits : List Bool) :
    ResidualPath startResidual (nullHistory bits) startResidual := by
  induction bits with
  | nil => exact PrefixResidual.Path.nil
  | cons bit bits induction =>
      exact PrefixResidual.Path.append (nullBlock_path bit) induction

private theorem path_classify {history : List (Stroke TagLetter 3)}
    (path : ResidualPath startResidual history startResidual) :
    ∃ bits, history = nullHistory bits := by
  by_cases empty : history = []
  · exact ⟨[], by simp [empty, nullHistory]⟩
  · obtain ⟨prior₂, before₂, last, historyEquality, path₂, lastStep⟩ :=
      path.snoc_of_ne_nil empty
    have rigid₂ := preserves_rightRigid path₂ start_rightRigid
    rcases enters_start rigid₂ lastStep with deepEntrance | wideEntrance
    · obtain ⟨rfl, rfl⟩ := deepEntrance
      obtain ⟨prior₁, before₁, middle, prior₂Equality, path₁, middleStep⟩ :=
        path₂.snoc_of_ne_nil (by
          intro empty₂
          subst prior₂
          have realized := path₂.realizes (left := []) (right := [.b]) (by rfl)
          simp [Residual.Realizes, deepResidual, Residual.leftWord,
            Residual.rightWord] at realized)
      have rigid₁ := preserves_rightRigid path₁ start_rightRigid
      obtain ⟨rfl, rfl⟩ := enters_deep rigid₁ middleStep
      obtain ⟨prior₀, before₀, first, prior₁Equality, path₀, firstStep⟩ :=
        path₁.snoc_of_ne_nil (by
          intro empty₁
          subst prior₁
          have realized := path₁.realizes (left := []) (right := [.b]) (by rfl)
          simp [Residual.Realizes, leftResidual, Residual.leftWord,
            Residual.rightWord] at realized)
      have rigid₀ := preserves_rightRigid path₀ start_rightRigid
      obtain ⟨rfl, rfl⟩ := enters_left rigid₀ firstStep
      obtain ⟨bits, priorEquality⟩ := path_classify path₀
      refine ⟨bits ++ [false], ?_⟩
      simp [historyEquality, prior₂Equality, prior₁Equality, priorEquality, nullHistory,
        nullHistory_append, nullBlock, nullBlockA, List.append_assoc]
    · obtain ⟨rfl, rfl⟩ := wideEntrance
      obtain ⟨prior₁, before₁, middle, prior₂Equality, path₁, middleStep⟩ :=
        path₂.snoc_of_ne_nil (by
          intro empty₂
          subst prior₂
          have realized := path₂.realizes (left := []) (right := [.b]) (by rfl)
          simp [Residual.Realizes, wideResidual, Residual.leftWord,
            Residual.rightWord] at realized)
      have rigid₁ := preserves_rightRigid path₁ start_rightRigid
      obtain ⟨rfl, rfl⟩ := enters_wide rigid₁ middleStep
      obtain ⟨prior₀, before₀, first, prior₁Equality, path₀, firstStep⟩ :=
        path₁.snoc_of_ne_nil (by
          intro empty₁
          subst prior₁
          have realized := path₁.realizes (left := []) (right := [.b]) (by rfl)
          simp [Residual.Realizes, leftResidual, Residual.leftWord,
            Residual.rightWord] at realized)
      have rigid₀ := preserves_rightRigid path₀ start_rightRigid
      obtain ⟨rfl, rfl⟩ := enters_left rigid₀ firstStep
      obtain ⟨bits, priorEquality⟩ := path_classify path₀
      refine ⟨bits ++ [true], ?_⟩
      simp [historyEquality, prior₂Equality, prior₁Equality, priorEquality, nullHistory,
        nullHistory_append, nullBlock, nullBlockB, List.append_assoc]
termination_by history.length
decreasing_by
  all_goals rw [historyEquality, prior₂Equality, prior₁Equality]
  all_goals simp

@[simp] theorem mixedNull_nullHistory (bits : List Bool) : mixedNull (nullHistory bits) := by
  rw [mixedNull_iff_path]
  exact nullHistory_path bits

theorem mixedNull_iff (history : List (Stroke TagLetter 3)) :
    mixedNull history ↔ ∃ bits, history = nullHistory bits := by
  rw [mixedNull_iff_path]
  constructor
  · exact path_classify
  · rintro ⟨bits, rfl⟩
    exact nullHistory_path bits

/-- The complete mixed terminal history with independently selected null blocks. -/
def terminalHistory (bits : List Bool) : List (Stroke TagLetter 3) :=
  prefixHistory ++ nullHistory bits

private theorem terminal_semantic_iff (history : List (Stroke TagLetter 3)) :
    (∃ first tail, history = first :: tail ∧
      consumed (first :: tail) ++ [.b] =
        .c :: nearyBody mixedBody first.head ++ [.b] ++
          produced (tagOutput mixedBody) tail) ↔
      ∃ nullTail, history = prefixHistory ++ nullTail ∧ mixedNull nullTail := by
  constructor
  · rintro ⟨first, tail, rfl, semantic⟩
    rcases first with ⟨firstHead, firstWake, firstWidth⟩
    have firstWakeLength : firstWake.length = 2 := by omega
    obtain ⟨firstWake₁, firstWake₂, rfl⟩ := List.length_eq_two.mp firstWakeLength
    have firstPrefix := congrArg (List.take 3) semantic
    cases firstHead <;> cases firstWake₁ <;> cases firstWake₂ <;>
      simp [consumed_cons, mixedBody, nearyBody,
        Stroke.letters] at firstPrefix
    simp [consumed_cons, mixedBody, nearyBody, Stroke.letters] at semantic
    cases tail with
    | nil => simp at semantic
    | cons second tail =>
        rcases second with ⟨secondHead, secondWake, secondWidth⟩
        have secondWakeLength : secondWake.length = 2 := by omega
        obtain ⟨secondWake₁, secondWake₂, rfl⟩ :=
          List.length_eq_two.mp secondWakeLength
        have secondPrefix := congrArg (List.take 3) semantic
        cases secondHead <;> cases secondWake₁ <;> cases secondWake₂ <;>
          simp [consumed_cons, produced_cons, tagOutput, nearyBody,
            Stroke.letters] at secondPrefix
        simp [consumed_cons, produced_cons, tagOutput, nearyBody,
          Stroke.letters] at semantic
        cases tail with
        | nil => simp at semantic
        | cons third nullTail =>
            rcases third with ⟨thirdHead, thirdWake, thirdWidth⟩
            have thirdWakeLength : thirdWake.length = 2 := by omega
            obtain ⟨thirdWake₁, thirdWake₂, rfl⟩ :=
              List.length_eq_two.mp thirdWakeLength
            have thirdPrefix := congrArg (List.take 3) semantic
            cases thirdHead <;> cases thirdWake₁ <;> cases thirdWake₂ <;>
              simp [consumed_cons, produced_cons, tagOutput, nearyBody,
                Stroke.letters] at thirdPrefix
            refine ⟨nullTail, ?_, ?_⟩
            · simp [prefixHistory, strokeCBC, strokeBCB, strokeBBB, stroke₃]
            · simpa [mixedNull, consumed_cons, produced_cons, mixedBody, tagOutput,
                nearyBody, Stroke.letters, List.append_assoc] using semantic
  · rintro ⟨nullTail, rfl, null⟩
    refine ⟨strokeCBC, strokeBCB :: strokeBBB :: nullTail, ?_, ?_⟩
    · rfl
    · simpa [prefixHistory, mixedNull, consumed_cons, produced_cons, mixedBody, tagOutput,
        nearyBody, Stroke.letters, strokeCBC, strokeBCB, strokeBBB, stroke₃,
        List.append_assoc] using null

/-- Complete semantic grammar for the mixed body. -/
theorem mixed_terminal_match_iff (word : List NearyTile) :
    spell (nearyUpper 3) word ++ nearyMarker 3 =
        spell (nearyLower 3 mixedBody) word ↔
      ∃ bits, word = tileHistory (terminalHistory bits) := by
  constructor
  · intro terminal
    obtain ⟨history, rfl⟩ :=
      tileHistory_of_terminal_match 3 mixedBody (by decide) word terminal
    have nonempty : history ≠ [] := by
      intro empty
      subst history
      simp [spell, nearyMarker] at terminal
    obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil nonempty
    have semantic :=
      (terminal_match_tileHistory_iff 3 mixedBody (by decide) first tail).mp terminal
    obtain ⟨nullTail, historyEquality, null⟩ :=
      (terminal_semantic_iff (first :: tail)).mp ⟨first, tail, rfl, semantic⟩
    obtain ⟨bits, rfl⟩ := (mixedNull_iff nullTail).mp null
    exact ⟨bits, by
      simpa [terminalHistory] using congrArg tileHistory historyEquality⟩
  · rintro ⟨bits, rfl⟩
    rw [terminalHistory, prefixHistory]
    apply (terminal_match_tileHistory_iff 3 mixedBody (by decide)
      strokeCBC (strokeBCB :: strokeBBB :: nullHistory bits)).mpr
    simpa [mixedNull, consumed_cons, produced_cons, mixedBody, tagOutput, nearyBody,
      Stroke.letters, strokeCBC, strokeBCB, strokeBBB, stroke₃, List.append_assoc] using
      mixedNull_nullHistory bits

/-! ## Canonical raw-control normal form -/

/-- A control word with every adjacent toggle pair scoured away. -/
inductive ToggleNormal : List PairedControl → Prop where
  | nil : ToggleNormal []
  | toggle : ToggleNormal [.toggle]
  | data (letter : TagLetter) {word : List PairedControl} :
      ToggleNormal word → ToggleNormal (.data letter :: word)
  | toggleData (letter : TagLetter) {word : List PairedControl} :
      ToggleNormal word →
        ToggleNormal (.toggle :: .data letter :: word)

/-- Delete adjacent phase-toggle pairs, from right to left. -/
def scourToggles : List PairedControl → List PairedControl
  | [] => []
  | .data letter :: word => .data letter :: scourToggles word
  | .toggle :: word =>
      match scourToggles word with
      | .toggle :: reduced => reduced
      | reduced => .toggle :: reduced

theorem scourToggles_normal (word : List PairedControl) :
    ToggleNormal (scourToggles word) := by
  induction word with
  | nil => exact ToggleNormal.nil
  | cons control word induction =>
      cases control with
      | data letter => exact ToggleNormal.data letter induction
      | toggle =>
          cases equality : scourToggles word with
          | nil => simpa [scourToggles, equality] using ToggleNormal.toggle
          | cons head tail =>
              cases head with
              | data letter =>
                  have normalData : ToggleNormal (.data letter :: tail) := by
                    simpa [equality] using induction
                  cases normalData with
                  | data _ tailNormal =>
                      simpa [scourToggles, equality] using
                        ToggleNormal.toggleData letter tailNormal
              | toggle =>
                  have normal : ToggleNormal (.toggle :: tail) := by
                    simpa [equality] using induction
                  cases normal with
                  | toggle => simpa [scourToggles, equality] using ToggleNormal.nil
                  | toggleData _ tailNormal =>
                      simpa [scourToggles, equality] using
                        ToggleNormal.data _ tailNormal

private theorem scourToggles_eq_self {word : List PairedControl}
    (normal : ToggleNormal word) : scourToggles word = word := by
  induction normal with
  | nil => rfl
  | toggle => rfl
  | data letter _ induction => simp [scourToggles, induction]
  | toggleData letter _ induction => simp [scourToggles, induction]

private theorem suffixDecode_scourToggles (word : List PairedControl) :
    suffixDecode (scourToggles word) = suffixDecode word := by
  induction word with
  | nil => rfl
  | cons control word induction =>
      cases control with
      | data letter => simp [scourToggles, suffixDecode, induction]
      | toggle =>
          have flipped := congrArg
            (fun decoded : PairPhase × List NearyTile => (decoded.1.flip, decoded.2)) induction
          cases equality : scourToggles word with
          | nil => simpa [scourToggles, suffixDecode, equality] using flipped
          | cons head tail =>
              cases head with
              | data letter =>
                  simpa [scourToggles, suffixDecode, equality] using flipped
              | toggle =>
                  cases tailDecoded : suffixDecode tail with
                  | mk tailPhase tailWord =>
                      cases wordDecoded : suffixDecode word with
                      | mk wordPhase wordWord =>
                          cases tailPhase <;> cases wordPhase <;>
                            simp [scourToggles, suffixDecode, equality, tailDecoded,
                              wordDecoded, PairPhase.flip] at induction ⊢ <;>
                            exact induction

/-- Phase carried by a decoded paired role. -/
private def tilePhase : NearyTile → PairPhase
  | .rule _ => .rule
  | .erase _ => .erase

/-- The unique toggle-normal control word with one prescribed full suffix decode. -/
private def rebuildControls : PairPhase → List NearyTile → List PairedControl
  | .rule, [] => []
  | .erase, [] => [.toggle]
  | .rule, tile :: word =>
      .toggle :: .data tile.letter :: rebuildControls (tilePhase tile) word
  | .erase, tile :: word =>
      .data tile.letter :: rebuildControls (tilePhase tile) word

private theorem suffixDecode_rebuildControls (phase : PairPhase) (word : List NearyTile) :
    suffixDecode (rebuildControls phase word) = (phase, word) := by
  induction word generalizing phase with
  | nil => cases phase <;> rfl
  | cons tile word induction =>
      cases phase <;> cases tile <;>
        simp [rebuildControls, suffixDecode, tilePhase, NearyTile.letter, induction,
          PairPhase.tile, PairPhase.flip]

private theorem rebuildControls_normal (phase : PairPhase) (word : List NearyTile) :
    ToggleNormal (rebuildControls phase word) := by
  induction word generalizing phase with
  | nil =>
      cases phase with
      | rule => simpa [rebuildControls] using ToggleNormal.nil
      | erase => simpa [rebuildControls] using ToggleNormal.toggle
  | cons tile word induction =>
      cases phase with
      | erase => exact ToggleNormal.data tile.letter (induction (tilePhase tile))
      | rule =>
          exact ToggleNormal.toggleData tile.letter (induction (tilePhase tile))

private theorem rebuildControls_suffixDecode {word : List PairedControl}
    (normal : ToggleNormal word) :
    rebuildControls (suffixDecode word).1 (suffixDecode word).2 = word := by
  induction normal with
  | nil => rfl
  | toggle => rfl
  | @data letter word _ induction =>
      cases decodedEquality : suffixDecode word with
      | mk phase decoded =>
          cases phase <;> cases letter <;>
            simp [suffixDecode, decodedEquality, rebuildControls, tilePhase,
              NearyTile.letter, PairPhase.tile] at induction ⊢ <;>
            exact induction
  | @toggleData letter word _ induction =>
      cases decodedEquality : suffixDecode word with
      | mk phase decoded =>
          cases phase <;> cases letter <;>
            simp [suffixDecode, decodedEquality, rebuildControls, tilePhase,
              NearyTile.letter, PairPhase.tile, PairPhase.flip] at induction ⊢ <;>
            exact induction

private theorem scourToggles_eq_rebuildControls (word : List PairedControl) :
    scourToggles word =
      rebuildControls (suffixDecode word).1 (suffixDecode word).2 := by
  have rebuilt := rebuildControls_suffixDecode (scourToggles_normal word)
  rw [suffixDecode_scourToggles] at rebuilt
  exact rebuilt.symm

/-- Canonical control spelling of one mixed terminal history. -/
def terminalControl (bits : List Bool) : List PairedControl :=
  historyControl (terminalHistory bits) ++ [.toggle]

private theorem historyControl_toggle_normal (history : List (Stroke TagLetter 3)) :
    ToggleNormal (historyControl history ++ [.toggle]) := by
  induction history with
  | nil => exact ToggleNormal.toggle
  | cons stroke history induction =>
      rcases stroke with ⟨head, wake, width⟩
      have wakeLength : wake.length = 2 := by omega
      obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wakeLength
      simpa [historyControl, strokeControl, Stroke.letters, List.append_assoc] using
        ToggleNormal.data head
          (ToggleNormal.toggleData wake₁
            (ToggleNormal.data wake₂ induction))

private theorem terminalControl_normal (bits : List Bool) :
    ToggleNormal (terminalControl bits) := by
  exact historyControl_toggle_normal (terminalHistory bits)

private theorem toggle_terminalControl_normal (bits : List Bool) :
    ToggleNormal (.toggle :: terminalControl bits) := by
  rw [terminalControl, terminalHistory, prefixHistory]
  change ToggleNormal
    (.toggle :: .data strokeCBC.head ::
      (strokeControl strokeCBC).tail ++
        historyControl (strokeBCB :: strokeBBB :: nullHistory bits) ++ [.toggle])
  apply ToggleNormal.toggleData strokeCBC.head
  simpa [historyControl, strokeControl, strokeCBC, stroke₃, List.append_assoc] using
    ToggleNormal.toggleData TagLetter.b
      (ToggleNormal.data TagLetter.c
        (historyControl_toggle_normal (strokeBCB :: strokeBBB :: nullHistory bits)))

theorem terminalControl_decode (bits : List Bool) :
    suffixDecode (terminalControl bits) =
      (.erase, tileHistory (terminalHistory bits)) := by
  simpa [terminalControl] using suffixDecode_historyControl (terminalHistory bits)

/-- Toggle reduction exposes exactly the two raw-control spellings of one decoded terminal
history: its canonical spelling and the same spelling with an irrelevant leading toggle. -/
theorem decode_eq_terminal_iff_scourToggles (word : List PairedControl) (bits : List Bool) :
    decodePairedWord word = tileHistory (terminalHistory bits) ↔
      scourToggles word = terminalControl bits ∨
        scourToggles word = .toggle :: terminalControl bits := by
  constructor
  · intro decodedEquality
    have rebuilt := scourToggles_eq_rebuildControls word
    cases suffixEquality : suffixDecode word with
    | mk phase decoded =>
        have decoded : decoded = tileHistory (terminalHistory bits) := by
          simpa [decodePairedWord, suffixEquality] using decodedEquality
        subst decoded
        cases phase with
        | erase =>
            left
            rw [rebuilt, suffixEquality]
            have canonical := rebuildControls_suffixDecode (terminalControl_normal bits)
            rw [terminalControl_decode] at canonical
            exact canonical
        | rule =>
            right
            rw [rebuilt, suffixEquality]
            have leadingDecode :
                suffixDecode (.toggle :: terminalControl bits) =
                  (.rule, tileHistory (terminalHistory bits)) := by
              rw [suffixDecode, terminalControl_decode]
              rfl
            have canonical :=
              rebuildControls_suffixDecode (toggle_terminalControl_normal bits)
            rw [leadingDecode] at canonical
            exact canonical
  · rintro (reducedEquality | reducedEquality)
    · have decoded := congrArg suffixDecode reducedEquality
      rw [suffixDecode_scourToggles, terminalControl_decode] at decoded
      exact congrArg Prod.snd decoded
    · have decoded := congrArg suffixDecode reducedEquality
      rw [suffixDecode_scourToggles] at decoded
      have roleEquality := congrArg Prod.snd decoded
      have leadingDecode :
          suffixDecode (.toggle :: terminalControl bits) =
            (.rule, tileHistory (terminalHistory bits)) := by
        rw [suffixDecode, terminalControl_decode]
        rfl
      rw [leadingDecode] at roleEquality
      simpa [decodePairedWord] using roleEquality

end MixedBranchingRecognizer

end MatrixMortality
