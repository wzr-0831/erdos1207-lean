import NormSeparation
import NumberFieldCoordinates
import NumberFieldBox
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Actual ideal norm lower bounds for lattice separation

This uses Mathlib's actual multiplicative ideal norm and principal-ideal norm
identity. No hypothetical norm-divisibility or preservation premise is used.
The real-embedding product identity is supplied by a separate actual
number-field coordinate bridge before the final packing theorem is composed.
-/

namespace JSP1012.IdealPacking
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Every nonzero element of an ideal has integer absolute norm at least the
absolute ideal norm. This is proved using actual ideal divisibility. -/
theorem absNorm_le_norm_natAbs (I : Ideal (𝓞 K)) {z : 𝓞 K}
    (hz : z ∈ I) (hz0 : z ≠ 0) :
    Ideal.absNorm I ≤ (Algebra.norm ℤ z).natAbs := by
  have hdvd : Ideal.absNorm I ∣ (Algebra.norm ℤ z).natAbs := by
    rw [← Ideal.absNorm_span_singleton]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).mpr hz)
  have hnorm : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz0
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hnorm) hdvd

/-- The actual norm lower bound on every distinct pair of elements of an ideal. -/
theorem difference_norm_lower (I : Ideal (𝓞 K)) {x y : 𝓞 K}
    (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
    Ideal.absNorm I ≤ (Algebra.norm ℤ (x - y)).natAbs :=
  absNorm_le_norm_natAbs I (I.sub_mem hx hy) (sub_ne_zero.mpr hxy)

/-- Nonzero integral ideals really have strictly positive ideal norm. -/
theorem ideal_norm_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < Ideal.absNorm I :=
  Nat.pos_of_ne_zero (fun hzero => hI (Ideal.absNorm_eq_zero_iff.mp hzero))

section TotallyReal
open NumberField
open scoped BigOperators
variable [IsTotallyReal K]

/-- In a totally real number field, all infinite places occur with multiplicity
one, so their number is the actual field degree. -/
theorem real_coordinate_count :
    Fintype.card (InfinitePlace K) = Module.finrank ℚ K := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

/-- The norm-product separation input is derived from actual ideal membership
and the proved number-field product formula, not supplied as a hypothesis. -/
theorem ideal_difference_product_lower (I : Ideal (𝓞 K)) {x y : 𝓞 K}
    (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace K,
      |NumberFieldCoordinates.realCoordinate x w - NumberFieldCoordinates.realCoordinate y w| := by
  rw [NumberFieldCoordinates.product_abs_coordinate_difference]
  exact (Nat.cast_le (α := ℝ)).mpr (difference_norm_lower I hx hy hxy)

/-- Actual ideal-lattice box upper bound, in exactly the LPZ root-norm form.
Every finite subset of the ideal lying in the Minkowski box satisfies it.
There is no hypothetical lattice-separation premise left in this statement. -/
theorem ideal_box_card_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (s : Finset (𝓞 K)) {X : ℝ} (hX : 0 ≤ X)
    (hmem : ∀ x, x ∈ s → x ∈ I)
    (hbox : ∀ x, x ∈ s → ∀ w : InfinitePlace K,
      NumberFieldCoordinates.realCoordinate x w ∈ Set.Icc (-X) X) :
    (s.card : ℝ) ≤ (1 + 2 * X /
      (Ideal.absNorm I : ℝ) ^ (1 / (Module.finrank ℚ K : ℝ))) ^ Module.finrank ℚ K := by
  have hA : (0 : ℝ) < (Ideal.absNorm I : ℝ) :=
    Nat.cast_pos.mpr (ideal_norm_pos I hI)
  have hproduct : ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
      (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace K,
        |NumberFieldCoordinates.realCoordinate x w - NumberFieldCoordinates.realCoordinate y w| := by
    intro x hx y hy hxy
    exact ideal_difference_product_lower I (hmem x hx) (hmem y hy) hxy
  have h := NormSeparation.card_le_box_bound_of_product_lower s
    NumberFieldCoordinates.realCoordinate hA hX hbox hproduct
  simpa only [real_coordinate_count (K := K)] using h

/-- Full ideal intersection with the Minkowski box, not just an arbitrary finite
subfamily. Finiteness and its exact set interpretation are already proved. -/
theorem idealBoxFinset_card_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {X : ℝ} (hX : 0 ≤ X) :
    ((NumberFieldBox.idealBoxFinset I X).card : ℝ) ≤ (1 + 2 * X /
      (Ideal.absNorm I : ℝ) ^ (1 / (Module.finrank ℚ K : ℝ))) ^ Module.finrank ℚ K := by
  apply ideal_box_card_le I hI (NumberFieldBox.idealBoxFinset I X) hX
  · intro x hx
    exact ((NumberFieldBox.mem_idealBoxFinset I X x).mp hx).1
  · intro x hx
    exact ((NumberFieldBox.mem_idealBoxFinset I X x).mp hx).2

end TotallyReal

end JSP1012.IdealPacking

#print axioms JSP1012.IdealPacking.absNorm_le_norm_natAbs
#print axioms JSP1012.IdealPacking.difference_norm_lower
#print axioms JSP1012.IdealPacking.ideal_norm_pos

#print axioms JSP1012.IdealPacking.real_coordinate_count
#print axioms JSP1012.IdealPacking.ideal_difference_product_lower
#print axioms JSP1012.IdealPacking.ideal_box_card_le

#print axioms JSP1012.IdealPacking.idealBoxFinset_card_le
