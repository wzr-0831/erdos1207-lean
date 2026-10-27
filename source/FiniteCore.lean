import FinitePairCount
import FiniteFibers
import FiniteCauchy
import DistanceInterface

/-!
# Composed finite-fiber collision bounds

All finite objects and all labelings are quantified. This proves the exact
counting step in LPZ26 §3. It does NOT assert the existence of the number-field
towers, the geometric Minkowski grid, the required lattice estimates, or the
robust all-subset distance-multiplicity theorem.
-/

namespace JSP1012

theorem countBelow_mono {n : Nat} {P Q : Nat → Bool}
    (h : ∀ i, i < n → P i = true → Q i = true) :
    countBelow n P ≤ countBelow n Q := by
  apply sumBelow_le
  intro i hi
  cases hp : P i with
  | false => simp
  | true => simp [h i hi hp]

theorem pairCount_mono {n : Nat} {R S : Nat → Nat → Bool}
    (h : ∀ i, i < n → ∀ j, j < n → R i j = true → S i j = true) :
    pairCount n R ≤ pairCount n S := by
  apply sumBelow_le
  intro i hi
  exact countBelow_mono (h i hi)

/-- Exact finite-fiber Cauchy bound after removing diagonal pairs. -/
theorem same_fiber_cauchy (n q : Nat) (A : Nat → Bool) (label : Nat → Nat)
    (hlabel : ∀ i, i < n → A i = true → label i < q) :
    (countBelow n A) ^ 2 - q * countBelow n A ≤
      q * pairCount n (Fibers.sameFiber A label) := by
  have h := Cauchy.collision_cauchy_sub q (Fibers.occupancy n A label)
  rw [Fibers.partition n q A label hlabel] at h
  unfold Cauchy.collisionSum at h
  rw [← Fibers.pair_count n q A label hlabel] at h
  exact h

/-- The LPZ26 size regime: `|A| ≥ 2q` leaves at least half the square count. -/
theorem same_fiber_lower (n q : Nat) (A : Nat → Bool) (label : Nat → Nat)
    (hlabel : ∀ i, i < n → A i = true → label i < q)
    (hsize : 2 * q ≤ countBelow n A) :
    (countBelow n A) ^ 2 ≤ 2 * q * pairCount n (Fibers.sameFiber A label) := by
  have hs : 2 * q ≤ sumBelow q (Fibers.occupancy n A label) := by
    rw [Fibers.partition n q A label hlabel]
    exact hsize
  have h := Cauchy.collision_lower_of_twice_bins_le q (Fibers.occupancy n A label) hs
  rw [Fibers.partition n q A label hlabel] at h
  unfold Cauchy.collisionSum at h
  rw [← Fibers.pair_count n q A label hlabel] at h
  exact h

/-- Collision pairs can be transferred to any relation known to contain them. -/
theorem relation_lower_of_same_fibers {n q : Nat} {A : Nat → Bool}
    {label : Nat → Nat} {R : Nat → Nat → Bool}
    (hlabel : ∀ i, i < n → A i = true → label i < q)
    (hsize : 2 * q ≤ countBelow n A)
    (hinclude : ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A label i j = true → R i j = true) :
    (countBelow n A) ^ 2 ≤ 2 * q * pairCount n R := by
  exact Nat.le_trans (same_fiber_lower n q A label hlabel hsize)
    (Nat.mul_le_mul_left (2 * q) (pairCount_mono hinclude))

end JSP1012

#print axioms JSP1012.same_fiber_cauchy
#print axioms JSP1012.same_fiber_lower
#print axioms JSP1012.relation_lower_of_same_fibers
