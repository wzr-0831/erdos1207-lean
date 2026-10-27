import RealFloorPacking
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Product separation and the concrete box-packing bound

In a nonempty finite coordinate type, a positive lower bound on the product of
absolute coordinate differences forces separation in at least one coordinate.
Composing with the actual floor-bin injection yields the real packing bound.
The root-scale corollary uses the proved real-rpow identity `(A^(1/d))^d=A`.

The product lower bound is an EXPLICIT hypothesis. This module does not assert
that it equals an algebraic norm or is bounded below by an ideal norm. The
coordinate type must be nonempty: an empty product is one but supplies no
coordinate in which separation could hold.
-/

namespace JSP1012.NormSeparation

open scoped BigOperators

/-- A positive product lower bound forces one coordinate to reach its scale.
Positivity of each factor is derived from the product bound, not assumed. -/
theorem exists_coordinate_of_product {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hproduct : a ^ Fintype.card ι ≤ ∏ i, |f i|) :
    ∃ i, a ≤ |f i| := by
  classical
  by_contra hno
  have hlt : ∀ i, |f i| < a := by
    intro i
    exact lt_of_not_ge (fun h => hno ⟨i, h⟩)
  have hproductpos : 0 < ∏ i, |f i| := (pow_pos ha _).trans_le hproduct
  have hfactorne : ∀ i, |f i| ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hproductpos.ne') i (Finset.mem_univ i)
  have hfactorpos : ∀ i ∈ (Finset.univ : Finset ι), 0 < |f i| := by
    intro i hi
    rcases (abs_nonneg (f i)).eq_or_lt with hz | hp
    · exact False.elim (hfactorne i hz.symm)
    · exact hp
  have hstrict := Finset.prod_lt_prod_of_nonempty₀ hfactorpos
    (fun i _ => hlt i) (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  have hstrict' : (∏ i, |f i|) < a ^ Fintype.card ι := by simpa using hstrict
  exact (not_lt_of_ge hproduct) hstrict'

/-- Product separation on every distinct selected pair implies actual coordinate
separation; repeated geometric points cannot satisfy the positive product bound. -/
theorem separated_of_product {α ι : Type*} [Fintype ι] [Nonempty ι]
    (s : Finset α) (p : α → ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hproduct : ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
      a ^ Fintype.card ι ≤ ∏ i, |p x i - p y i|) :
    RealPacking.Separated s p a := by
  intro x hx y hy hxy
  exact exists_coordinate_of_product (fun i => p x i - p y i) ha (hproduct x hx y hy hxy)

/-- Complete finite product-to-packing implication, with the arithmetic input
explicit and no ideal norm or field embedding identified by assumption. -/
theorem card_le_box_bound_of_product {α ι : Type*} [Fintype ι] [Nonempty ι]
    (s : Finset α) (p : α → ι → ℝ) {a X : ℝ}
    (ha : 0 < a) (hX : 0 ≤ X)
    (hbox : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc (-X) X)
    (hproduct : ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
      a ^ Fintype.card ι ≤ ∏ i, |p x i - p y i|) :
    (s.card : ℝ) ≤ (1 + 2 * X / a) ^ Fintype.card ι :=
  RealPacking.card_le_real_box_bound s p ha hX hbox
    (separated_of_product s p ha hproduct)

/-- The positive real root scale has exactly the prescribed `d`-th power. -/
theorem root_scale_pow {ι : Type*} [Fintype ι] [Nonempty ι]
    {A : ℝ} (hA : 0 < A) :
    (A ^ (1 / (Fintype.card ι : ℝ))) ^ Fintype.card ι = A := by
  simpa only [one_div] using
    (Real.rpow_inv_natCast_pow hA.le (Fintype.card_ne_zero : Fintype.card ι ≠ 0))

/-- A genuine product lower bound `A>0` gives separation at scale `A^(1/d)`. -/
theorem separated_of_product_lower {α ι : Type*} [Fintype ι] [Nonempty ι]
    (s : Finset α) (p : α → ι → ℝ) {A : ℝ} (hA : 0 < A)
    (hproduct : ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
      A ≤ ∏ i, |p x i - p y i|) :
    RealPacking.Separated s p (A ^ (1 / (Fintype.card ι : ℝ))) := by
  apply separated_of_product s p (Real.rpow_pos_of_pos hA _)
  intro x hx y hy hxy
  rw [root_scale_pow (ι := ι) hA]
  exact hproduct x hx y hy hxy

/-- The LPZ-shaped packing estimate with the real root scale proved, not postulated. -/
theorem card_le_box_bound_of_product_lower {α ι : Type*} [Fintype ι] [Nonempty ι]
    (s : Finset α) (p : α → ι → ℝ) {A X : ℝ}
    (hA : 0 < A) (hX : 0 ≤ X)
    (hbox : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc (-X) X)
    (hproduct : ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y →
      A ≤ ∏ i, |p x i - p y i|) :
    (s.card : ℝ) ≤
      (1 + 2 * X / A ^ (1 / (Fintype.card ι : ℝ))) ^ Fintype.card ι :=
  RealPacking.card_le_real_box_bound s p (Real.rpow_pos_of_pos hA _) hX hbox
    (separated_of_product_lower s p hA hproduct)

/-- Dimension zero really invalidates the product-to-coordinate inference. -/
theorem zero_dimension_counterexample :
    (1 : ℝ) ^ Fintype.card (Fin 0) ≤ (∏ _i : Fin 0, |(0 : ℝ)|) ∧
      ¬ (∃ _i : Fin 0, (1 : ℝ) ≤ |(0 : ℝ)|) := by simp

end JSP1012.NormSeparation

#print axioms JSP1012.NormSeparation.exists_coordinate_of_product
#print axioms JSP1012.NormSeparation.separated_of_product
#print axioms JSP1012.NormSeparation.card_le_box_bound_of_product
#print axioms JSP1012.NormSeparation.root_scale_pow
#print axioms JSP1012.NormSeparation.card_le_box_bound_of_product_lower
#print axioms JSP1012.NormSeparation.zero_dimension_counterexample
