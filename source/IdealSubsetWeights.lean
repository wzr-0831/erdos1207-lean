import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Selected square divisibility gives the actual extra ideal factor

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
A coordinated successful compiler run and axiom audit are still required.

For a finite coordinate family of pairwise COPRIME actual ideals, membership
in their total product and in each selected ideal square is equivalent to
membership in the total product times the selected product. Coprime powers
turn the exponent-one/exponent-two product into an actual intersection.
There is no valuation, UFD, complete splitting, root, or global factorization
hypothesis hidden in this step.

The finite index set is retained throughout: equal numerical norms never merge
coordinates. Pairwise coprimality is required on distinct indices, not inferred
from distinct norms (nor from an unproved pairwise-distinctness claim).
-/

noncomputable section

namespace JSP1012.IdealSubsetWeights

open scoped BigOperators

/-- Elementary product identity with every selected coordinate doubled.
It is valid in any commutative monoid and retains the coordinate indices. -/
theorem product_selected_squares {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s t : Finset ι) (ht : t ⊆ s) (P : ι → M) :
    (∏ i ∈ s, P i ^ (if i ∈ t then 2 else 1)) =
      (∏ i ∈ s, P i) * ∏ i ∈ t, P i := by
  have hfilter : s.filter (fun i => i ∈ t) = t := Finset.filter_mem_eq_of_subset ht
  calc
    (∏ i ∈ s, P i ^ (if i ∈ t then 2 else 1)) =
        ∏ i ∈ s, P i * (if i ∈ t then P i else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hit : i ∈ t <;> simp only [hit, if_true, if_false, pow_two, pow_one, mul_one]
    _ = (∏ i ∈ s, P i) * ∏ i ∈ s, (if i ∈ t then P i else 1) :=
      Finset.prod_mul_distrib
    _ = (∏ i ∈ s, P i) * ∏ i ∈ t, P i := by
      rw [← Finset.prod_filter (fun i => i ∈ t) P, hfilter]

section Membership

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- Membership in an ideal product implies membership in every factor.
This direction does not need coprimality. -/
theorem mem_each_of_mem_product (s : Finset ι) (P : ι → Ideal R) {z : R}
    (hz : z ∈ ∏ i ∈ s, P i) {i : ι} (hi : i ∈ s) : z ∈ P i := by
  have hle : (∏ j ∈ s, P j) ≤ P i := Ideal.prod_le_inf.trans (Finset.inf_le hi)
  exact hle hz

/-- The required LPZ `Q*a` membership step, proved for actual ideal products. -/
theorem mem_total_mul_selected_of_squares (s t : Finset ι) (ht : t ⊆ s)
    (P : ι → Ideal R)
    (hcoprime : (s : Set ι).Pairwise (fun i j => IsCoprime (P i) (P j)))
    {z : R} (hz : z ∈ ∏ i ∈ s, P i)
    (hsquares : ∀ i ∈ t, z ∈ P i ^ 2) :
    z ∈ (∏ i ∈ s, P i) * ∏ i ∈ t, P i := by
  have hpowers : (s : Set ι).Pairwise (fun i j =>
      IsCoprime (P i ^ (if i ∈ t then 2 else 1)) (P j ^ (if j ∈ t then 2 else 1))) := by
    intro i hi j hj hij
    exact (hcoprime hi hj hij).pow
  have hzpower : z ∈ ∏ i ∈ s, P i ^ (if i ∈ t then 2 else 1) := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hpowers]
    simp only [Submodule.mem_iInf]
    intro i hi
    by_cases hit : i ∈ t
    · simpa only [hit, if_true] using hsquares i hit
    · simpa only [hit, if_false, pow_one] using mem_each_of_mem_product s P hz hi
  rw [product_selected_squares s t ht P] at hzpower
  exact hzpower

/-- Conversely, the extra selected product really provides every selected square. -/
theorem mem_and_squares_of_mem_total_mul_selected (s t : Finset ι) (ht : t ⊆ s)
    (P : ι → Ideal R) {z : R}
    (hz : z ∈ (∏ i ∈ s, P i) * ∏ i ∈ t, P i) :
    (z ∈ ∏ i ∈ s, P i) ∧ ∀ i ∈ t, z ∈ P i ^ 2 := by
  have hzpower : z ∈ ∏ i ∈ s, P i ^ (if i ∈ t then 2 else 1) := by
    rw [product_selected_squares s t ht P]
    exact hz
  refine ⟨Ideal.mul_le_left hz, ?_⟩
  intro i hit
  have hi := mem_each_of_mem_product s
    (fun j => P j ^ (if j ∈ t then 2 else 1)) hzpower (ht hit)
  simpa only [hit, if_true] using hi

/-- Exact membership equivalence, preserving all selected coordinate occurrences. -/
theorem mem_total_mul_selected_iff (s t : Finset ι) (ht : t ⊆ s)
    (P : ι → Ideal R)
    (hcoprime : (s : Set ι).Pairwise (fun i j => IsCoprime (P i) (P j))) {z : R} :
    z ∈ (∏ i ∈ s, P i) * ∏ i ∈ t, P i ↔
      (z ∈ ∏ i ∈ s, P i) ∧ ∀ i ∈ t, z ∈ P i ^ 2 := by
  constructor
  · exact mem_and_squares_of_mem_total_mul_selected s t ht P
  · intro h
    exact mem_total_mul_selected_of_squares s t ht P hcoprime h.1 h.2

end Membership

section Norm

variable {R ι : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Infinite R] [DecidableEq ι]

/-- Actual absolute-norm multiplicativity gives the full weight formula.
No positivity assumptions are needed for this identity, even if a norm is zero. -/
theorem absNorm_total_mul_selected (s t : Finset ι) (P : ι → Ideal R) :
    ((∏ i ∈ s, P i) * ∏ i ∈ t, P i).absNorm =
      (∏ i ∈ s, (P i).absNorm) * ∏ i ∈ t, (P i).absNorm := by
  rw [map_mul, map_prod, map_prod]

/-- Equivalent exponent-weight form, derived from the actual ideal identity. -/
theorem absNorm_selected_squares (s t : Finset ι) (ht : t ⊆ s) (P : ι → Ideal R) :
    (∏ i ∈ s, P i ^ (if i ∈ t then 2 else 1)).absNorm =
      (∏ i ∈ s, (P i).absNorm) * ∏ i ∈ t, (P i).absNorm := by
  rw [product_selected_squares s t ht P, absNorm_total_mul_selected]

/-- Positive coordinate norms give a genuinely positive `Q*a` norm. -/
theorem absNorm_total_mul_selected_pos (s t : Finset ι) (ht : t ⊆ s)
    (P : ι → Ideal R) (hpositive : ∀ i ∈ s, 0 < (P i).absNorm) :
    0 < ((∏ i ∈ s, P i) * ∏ i ∈ t, P i).absNorm := by
  rw [absNorm_total_mul_selected]
  exact Nat.mul_pos (Finset.prod_pos hpositive)
    (Finset.prod_pos (fun i hi => hpositive i (ht hi)))

end Norm
end JSP1012.IdealSubsetWeights

#print axioms JSP1012.IdealSubsetWeights.product_selected_squares
#print axioms JSP1012.IdealSubsetWeights.mem_total_mul_selected_of_squares
#print axioms JSP1012.IdealSubsetWeights.mem_total_mul_selected_iff
#print axioms JSP1012.IdealSubsetWeights.absNorm_total_mul_selected
#print axioms JSP1012.IdealSubsetWeights.absNorm_total_mul_selected_pos
