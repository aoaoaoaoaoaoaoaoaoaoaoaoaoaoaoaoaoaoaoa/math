import MatrixMortality.Undecidability.NearySource
import MatrixMortality.Undecidability.UniversalTwoTag

/-!
# A fixed universal Neary source

The fixed universal two-tag system is compiled through Cook's cyclic-tag construction and
Neary's restricted binary-tag construction. Protected execution gives the forward implication.
The cyclic firing reflection theorem and Neary's arbitrary-execution converse give the reverse
implication.
-/

namespace MatrixMortality
namespace Undecidability
namespace UniversalNeary

open scoped Classical

/-- Cook–Neary compilation of the verified universal two-tag source. -/
noncomputable def source : RestrictedTagSource Nat.Partrec.Code CodeHalts :=
  NearyCompiler.compile UniversalTwoTag.source

/-- The emitted restricted binary-tag instance halts exactly for accepted source codes. -/
theorem tagHaltsFrom_iff_codeHalts (index : Nat.Partrec.Code) :
    TagHaltsFrom source.width (tagOutput (source.body index))
        ((source.body index).drop (source.width - 1) ++ [.b]) ↔
      CodeHalts index :=
  source.halts_iff index

end UniversalNeary
end Undecidability
end MatrixMortality
