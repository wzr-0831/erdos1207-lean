import FinitePairCount
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Prod

/-!
# Finset interpretations of the independently verified Std counts

This module gives exact actual finite-set cardinalities, so the indexed finite
certificate can later be instantiated without pretending its mask cardinality
or ordered-pair multiplicity equals a geometric cardinality by definition.
It does not supply a field-point enumeration or the geometric construction.
-/

namespace JSP1012.FinsetCounts
open scoped BigOperators

/-- The elementary Std finite sum is the ordinary Finset range sum. -/
theorem sumBelow_eq_sum_range (n : Nat) (f : Nat → Nat) :
    sumBelow n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow_succ, ih, Finset.sum_range_succ]

/-- The Boolean mask counts its actual selected finite set. -/
theorem countBelow_eq_filter_card (n : Nat) (A : Nat → Bool) :
    countBelow n A = ((Finset.range n).filter (fun i => A i = true)).card := by
  rw [countBelow, sumBelow_eq_sum_range, Finset.card_filter]

/-- Ordered pair counting is the cardinality of an actual filtered PRODUCT,
not an unordered-pair finset and not an implicitly diagonal-free product. -/
theorem pairCount_eq_product_filter_card (n : Nat) (R : Nat → Nat → Bool) :
    pairCount n R = (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun ij => R ij.1 ij.2 = true)).card := by
  rw [pairCount, sumBelow_eq_sum_range, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  exact sumBelow_eq_sum_range n (fun j => if R i j then 1 else 0)

/-- The exact selected, distinct, fixed-label pair set. Every restriction in
the Std definition survives in the actual Finset cardinality. -/
theorem distanceMultiplicity_eq_product_filter_card {D : Type} [DecidableEq D]
    (n : Nat) (A : Nat → Bool) (d : Nat → Nat → D) (r : D) :
    distanceMultiplicity n A d r =
      (((Finset.range n) ×ˢ (Finset.range n)).filter (fun ij =>
        A ij.1 = true ∧ A ij.2 = true ∧ ij.1 ≠ ij.2 ∧ d ij.1 ij.2 = r)).card := by
  rw [distanceMultiplicity, pairCount_eq_product_filter_card]
  congr 1
  ext ij
  simp only [Finset.mem_filter, restrictRelation, distanceRelation, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

end JSP1012.FinsetCounts

#print axioms JSP1012.FinsetCounts.countBelow_eq_filter_card
#print axioms JSP1012.FinsetCounts.pairCount_eq_product_filter_card
#print axioms JSP1012.FinsetCounts.distanceMultiplicity_eq_product_filter_card
