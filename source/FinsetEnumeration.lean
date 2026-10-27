import FinsetCountBridge
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual finite enumerations with bounded-prefix and eligible-label guards

Source preparation. Default values are used ONLY outside the finite prefix or
outside the actual candidate set. Injectivity and inverse lemmas explicitly
require the corresponding bounds/membership, never a global fallback claim.
-/

noncomputable section

namespace JSP1012.FinsetEnumeration

variable {α : Type*}

def equivalence (s : Finset α) : s ≃ Fin s.card := Finset.equivFinOfCardEq rfl

def pointAt (s : Finset α) (fallback : α) (i : ℕ) : α :=
  if hi : i < s.card then ((equivalence s).symm ⟨i, hi⟩).val else fallback

theorem pointAt_mem (s : Finset α) (fallback : α) {i : ℕ} (hi : i < s.card) :
    pointAt s fallback i ∈ s := by
  simp only [pointAt, dif_pos hi]
  exact ((equivalence s).symm ⟨i, hi⟩).property

theorem pointAt_injective (s : Finset α) (fallback : α) {i j : ℕ}
    (hi : i < s.card) (hj : j < s.card)
    (heq : pointAt s fallback i = pointAt s fallback j) : i = j := by
  simp only [pointAt, dif_pos hi, dif_pos hj] at heq
  have h := (equivalence s).symm.injective (Subtype.ext heq)
  exact congrArg Fin.val h

theorem pointAt_surjective (s : Finset α) (fallback : α) {x : α} (hx : x ∈ s) :
    ∃ i, i < s.card ∧ pointAt s fallback i = x := by
  let i := equivalence s ⟨x, hx⟩
  refine ⟨i.val, i.isLt, ?_⟩
  simp only [pointAt, dif_pos i.isLt]
  exact congrArg Subtype.val ((equivalence s).symm_apply_apply ⟨x, hx⟩)

/-- A finite candidate index is meaningful only on actual candidate members. -/
def index (s : Finset α) (x : α) : ℕ := by
  classical
  exact if hx : x ∈ s then (equivalence s ⟨x, hx⟩).val else 0

theorem index_lt (s : Finset α) {x : α} (hx : x ∈ s) : index s x < s.card := by
  classical
  simp only [index, dif_pos hx]
  exact (equivalence s ⟨x, hx⟩).isLt

theorem index_injective_on_members (s : Finset α) {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (heq : index s x = index s y) : x = y := by
  classical
  simp only [index, dif_pos hx, dif_pos hy] at heq
  have h := (equivalence s).injective (Fin.ext heq)
  exact congrArg Subtype.val h

theorem pointAt_index (s : Finset α) (fallback : α) {x : α} (hx : x ∈ s) :
    pointAt s fallback (index s x) = x := by
  classical
  simp only [index, dif_pos hx, pointAt, dif_pos (equivalence s ⟨x, hx⟩).isLt]
  exact congrArg Subtype.val ((equivalence s).symm_apply_apply ⟨x, hx⟩)

/-- Indexed counting is exactly the actual filtered-cardinality count, for any
predicate on any universe of actual candidate values. -/
theorem countBelow_eq_filter_card (s : Finset α) (fallback : α) (P : α → Prop)
    [DecidablePred P] :
    countBelow s.card (fun i => decide (P (pointAt s fallback i))) = (s.filter P).card := by
  classical
  rw [FinsetCounts.countBelow_eq_filter_card]
  apply Finset.card_bij (fun i _ => pointAt s fallback i)
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr
      ⟨pointAt_mem s fallback (Finset.mem_range.mp hi'.1), by simpa using hi'.2⟩
  · intro i hi j hj hij
    exact pointAt_injective s fallback
      (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
  · intro x hx
    obtain ⟨i, hi, heq⟩ := pointAt_surjective s fallback (Finset.mem_filter.mp hx).1
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, heq⟩
    simpa only [heq, decide_eq_true_eq] using (Finset.mem_filter.mp hx).2

/-- Enumerating a selected finite set directly avoids an unproved mask-cardinality
identification. Only the actual finite prefix is selected. -/
theorem countBelow_true (s : Finset α) : countBelow s.card (fun _ => true) = s.card := by
  rw [FinsetCounts.countBelow_eq_filter_card]
  simp

/-- Actual point-set freeness transfers through the PROVED bounded enumeration.
The true-distance type stays universe0, as required by the Std finite core. -/
theorem indexed_free_of_free {D : Type} (s : Finset α) (fallback : α)
    (distance : α → α → D)
    (hfree : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s,
      x ≠ y → x ≠ z → y ≠ z → distance x y ≠ distance x z) :
    IsoscelesFree s.card (fun _ => true)
      (fun i j => distance (pointAt s fallback i) (pointAt s fallback j)) := by
  intro i hi _ j hj _ k hk _ hij hik hjk
  apply hfree _ (pointAt_mem s fallback hi) _ (pointAt_mem s fallback hj)
    _ (pointAt_mem s fallback hk)
  · exact fun h => hij (pointAt_injective s fallback hi hj h)
  · exact fun h => hik (pointAt_injective s fallback hi hk h)
  · exact fun h => hjk (pointAt_injective s fallback hj hk h)

end JSP1012.FinsetEnumeration

#print axioms JSP1012.FinsetEnumeration.pointAt_injective
#print axioms JSP1012.FinsetEnumeration.index_injective_on_members
#print axioms JSP1012.FinsetEnumeration.countBelow_eq_filter_card
#print axioms JSP1012.FinsetEnumeration.indexed_free_of_free
