import MatrixMortality.NearyEncoding

/-!
# Swapped-setter fringe languages

The depth-one setter comparison leaves one upper word, one lower word, and a bounded suffix.
This file owns their body-independent regular languages and the ternary code read by the swapped
setter.  Arithmetic classification belongs in `SwappedSetterFringe`.
-/

namespace MatrixMortality.SwappedSetterFringe

/-- Ternary code after exchanging the two binary digits. -/
def swappedCode (word : List Bool) : Nat :=
  ternaryCode (word.map Bool.not)

/-- Body-independent lower block at a phase of the Neary spelling. -/
def fringeBlock : Bool → List Bool
  | false => [false]
  | true => [true, true, false]

/-- A lower fringe may stop at any point inside a sequence of complete lower blocks. -/
def SourceFringe (word : List Bool) : Prop :=
  ∃ phases, word <+: spell fringeBlock phases

/-- Final bounded window of a body-independent lower spelling ending in an erasure. -/
def BlockTargetFringe (width : Nat) (word : List Bool) : Prop :=
  ∃ phases,
    phases.getLast? = some false ∧
      word = (spell fringeBlock phases).rtake width

/-- Necessary normal form of a physical target fringe ending in an erasure.  A preceding rule
block contributes either no `true`, a complete final pair, or the right member of a pair cut by
the width boundary.  The prefix before a complete pair may come from an encoded appendant. -/
def TargetFringe (width : Nat) (word : List Bool) : Prop :=
  word.length ≤ width ∧
    ((∃ zeros,
        2 ≤ zeros ∧
          word = List.replicate zeros false) ∨
      (∃ front zeros,
        2 ≤ zeros ∧
          word = front ++ [true, true] ++ List.replicate zeros false) ∨
      (word.length = width ∧
        word = true :: List.replicate (width - 1) false))

/-- The two possible shapes of the maximal unmatched upper fringe. -/
def UpperFringe (β : Nat) (word : List Bool) : Prop :=
  word = tagCode β .b ∨
    ∃ ones,
      2 ≤ ones ∧
        ones ≤ β + 2 ∧
          word = List.replicate ones true ++ List.replicate (β + 2 - ones) false

end MatrixMortality.SwappedSetterFringe
