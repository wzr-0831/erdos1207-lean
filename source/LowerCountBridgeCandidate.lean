import LowerCountCandidate
import NumberFieldBox

/-!
# Uncompiled bridge to the current JSP1012 coordinate-box definition

This is newly written glue, not an upstream theorem or a verified result.
The source-only lower-bound candidate must be compiled separately first.
-/

namespace JSP1012.NumberFieldBox

open NumberField NumberFieldCoordinates

theorem boxFinset_eq_sumProduct_boxAdd (K : Type*) [Field K] [NumberField K]
    [IsTotallyReal K] (X : ℝ) :
    boxFinset K X = SumProduct.boxAdd K X := by
  ext x
  rw [mem_boxFinset, SumProduct.mem_boxAdd]
  constructor
  · intro hx w
    rw [← abs_realCoordinate]
    exact abs_le.mpr (hx w)
  · intro hx w
    exact abs_le.mp (by rw [abs_realCoordinate]; exact hx w)

theorem boxFinset_card_ge_discriminant (K : Type*) [Field K] [NumberField K]
    [IsTotallyReal K] (X : ℝ) (hX : 0 ≤ X) :
    X ^ Module.finrank ℚ K / Real.sqrt |(NumberField.discr K : ℝ)| ≤
      (boxFinset K X).card := by
  rw [boxFinset_eq_sumProduct_boxAdd]
  exact SumProduct.boxAdd_card_ge rfl X hX

end JSP1012.NumberFieldBox

#print axioms JSP1012.NumberFieldBox.boxFinset_eq_sumProduct_boxAdd
#print axioms JSP1012.NumberFieldBox.boxFinset_card_ge_discriminant
