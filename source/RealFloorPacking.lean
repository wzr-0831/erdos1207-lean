import FloorBins
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card

/-!
# Concrete real-coordinate floor packing

An a-separated finite family in a closed d-dimensional box has cardinality at
most `(1 + 2*X/a)^d`. The proof is an actual injection into the finite grid of
floor bins, not a measure/packing axiom. Arbitrary finite coordinate types,
including the empty coordinate type, are allowed. The point enumeration need
not be separately assumed injective: positive coordinate separation implies
that property on the finite family.

This is the geometric packing component of the LPZ ideal-lattice upper bound.
The arithmetic proof that ideal norms supply separation remains separate.
-/

namespace JSP1012.RealPacking

/-- Separation means some coordinate differs by at least `a` for every two
DISTINCT original points. This rules out repeated geometric points. -/
def Separated {α ι : Type*} (s : Finset α) (p : α → ι → ℝ) (a : ℝ) : Prop :=
  ∀ x, x ∈ s → ∀ y, y ∈ s → x ≠ y → ∃ i, a ≤ |p x i - p y i|

/-- The genuine finite grid injection, before passing to a real upper bound. -/
theorem card_le_bins_pow {α ι : Type*} [Fintype ι]
    (s : Finset α) (p : α → ι → ℝ) {a X : ℝ}
    (ha : 0 < a) (hX : 0 ≤ X)
    (hbox : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc (-X) X)
    (hsep : Separated s p a) :
    s.card ≤ FloorBins.bins a X ^ Fintype.card ι := by
  classical
  let f : ↥s → (ι → Fin (FloorBins.bins a X)) := fun x i =>
    ⟨FloorBins.bin a X (p x.val i), FloorBins.bin_lt ha hX (hbox x.val x.property i)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases heq : x.val = y.val
    · exact Subtype.ext heq
    · obtain ⟨i, hgap⟩ := hsep x.val x.property y.val y.property heq
      have hbin : FloorBins.bin a X (p x.val i) = FloorBins.bin a X (p y.val i) :=
        congrArg Fin.val (congrFun hxy i)
      have hsmall := FloorBins.same_bin_abs_sub_lt ha
        (hbox x.val x.property i) (hbox y.val y.property i) hbin
      exact False.elim (not_lt_of_ge hgap hsmall)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hcard

/-- Exact LPZ packing bound, valid at closed endpoints, at X=0 and in dimension0. -/
theorem card_le_real_box_bound {α ι : Type*} [Fintype ι]
    (s : Finset α) (p : α → ι → ℝ) {a X : ℝ}
    (ha : 0 < a) (hX : 0 ≤ X)
    (hbox : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc (-X) X)
    (hsep : Separated s p a) :
    (s.card : ℝ) ≤ (1 + 2 * X / a) ^ Fintype.card ι := by
  have hn := card_le_bins_pow s p ha hX hbox hsep
  have hc : (s.card : ℝ) ≤ (FloorBins.bins a X : ℝ) ^ Fintype.card ι := by
    have h := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_pow] using h
  exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (FloorBins.bins_le_real ha hX) _)

/-- A zero-dimensional finite separated family really has at most one point. -/
theorem zero_dimension_card_le_one {α : Type*} (s : Finset α)
    (p : α → Fin 0 → ℝ) {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X)
    (hbox : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc (-X) X)
    (hsep : Separated s p a) : s.card ≤ 1 := by
  simpa using card_le_bins_pow s p ha hX hbox hsep

/-- A zero-width box has at most one positively separated point in every dimension. -/
theorem zero_width_card_le_one {α ι : Type*} [Fintype ι]
    (s : Finset α) (p : α → ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hbox : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc 0 0)
    (hsep : Separated s p a) : s.card ≤ 1 := by
  have hb : ∀ x, x ∈ s → ∀ i, p x i ∈ Set.Icc (-(0 : ℝ)) 0 := by
    simpa only [neg_zero] using hbox
  have hn := card_le_bins_pow s p ha (le_refl 0) hb hsep
  simpa [FloorBins.bins] using hn

end JSP1012.RealPacking

#print axioms JSP1012.RealPacking.card_le_bins_pow
#print axioms JSP1012.RealPacking.card_le_real_box_bound
#print axioms JSP1012.RealPacking.zero_dimension_card_le_one
#print axioms JSP1012.RealPacking.zero_width_card_le_one
