import FiniteCore

/-!
# The finite weighted-overlap sieve in LPZ26, section 3

A family of relations may overlap. We count its incidences WITH multiplicity,
then bound that multiplicity by a weight depending only on the exact distance
label. Finally we partition by that label and use its maximum pair multiplicity.
No CRT, number field, lattice bound, or geometric construction is assumed as an
axiom. All hypotheses below are explicit finite combinatorial data.
-/

namespace JSP1012.Sieve
open JSP1012

/-- Number of family members containing the ordered pair `(i,j)`. -/
def overlap (families : Nat) (R : Nat → Nat → Nat → Bool) (i j : Nat) : Nat :=
  countBelow families (fun e => R e i j)

/-- Ordered-pair count of a fixed exact label in a selected pair relation. -/
def pairFiber (n : Nat) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (r : Nat) : Nat :=
  pairCount n (fun i j => eligible i j && decide (label i j = r))

/-- The weighted sum over eligible ordered pairs. -/
def pairWeight (n : Nat) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (w : Nat → Nat) : Nat :=
  sumBelow n (fun i => sumBelow n (fun j => if eligible i j then w (label i j) else 0))

/-- Double counting keeps all overlaps, instead of falsely treating the family
as disjoint. -/
theorem family_incidence (families n : Nat) (R : Nat → Nat → Nat → Bool) :
    sumBelow families (fun e => pairCount n (R e)) =
      sumBelow n (fun i => sumBelow n (fun j => overlap families R i j)) := by
  unfold pairCount countBelow overlap
  rw [Fibers.sum_swap families n]
  apply sumBelow_congr
  intro i hi
  exact Fibers.sum_swap families n _

/-- Exact weighted partition of ordered pairs by their labels. -/
theorem pair_weight_partition (n q : Nat) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (w : Nat → Nat)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → label i j < q) :
    sumBelow q (fun r => pairFiber n eligible label r * w r) =
      pairWeight n eligible label w := by
  calc
    _ = sumBelow q (fun r => sumBelow n (fun i =>
        countBelow n (fun j => eligible i j && decide (label i j = r)) * w r)) := by
      apply sumBelow_congr
      intro r hr
      exact (Fibers.sum_mul_right n _ (w r)).symm
    _ = sumBelow n (fun i => sumBelow q (fun r =>
        countBelow n (fun j => eligible i j && decide (label i j = r)) * w r)) :=
      Fibers.sum_swap q n _
    _ = _ := by
      apply sumBelow_congr
      intro i hi
      exact Fibers.weighted_partition n q (eligible i) (label i) w (hlabel i hi)

/-- An overlap weight and a uniform exact-label multiplicity bound control the
TOTAL family incidence. This is the finite middle inequality of LPZ26 section 3. -/
theorem weighted_overlap_bound (families n q : Nat)
    (R : Nat → Nat → Nat → Bool) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (w : Nat → Nat) (mu : Nat)
    (hinclude : ∀ e, e < families → ∀ i, i < n → ∀ j, j < n →
      R e i j = true → eligible i j = true)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → label i j < q)
    (hoverlap : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      overlap families R i j ≤ w (label i j))
    (hfiber : ∀ r, r < q → pairFiber n eligible label r ≤ mu) :
    sumBelow families (fun e => pairCount n (R e)) ≤ mu * sumBelow q w := by
  calc
    _ = sumBelow n (fun i => sumBelow n (fun j => overlap families R i j)) :=
      family_incidence families n R
    _ ≤ pairWeight n eligible label w := by
      apply sumBelow_le
      intro i hi
      apply sumBelow_le
      intro j hj
      cases hel : eligible i j with
      | true => simpa [hel] using hoverlap i hi j hj hel
      | false =>
        have hz : overlap families R i j = 0 := by
          apply countBelow_zero_of
          intro e he
          cases hR : R e i j with
          | false => rfl
          | true => have := hinclude e he i hi j hj hR; simp_all
        simp [hz]
    _ = sumBelow q (fun r => pairFiber n eligible label r * w r) :=
      (pair_weight_partition n q eligible label w hlabel).symm
    _ ≤ sumBelow q (fun r => mu * w r) := by
      apply sumBelow_le
      intro r hr
      exact Nat.mul_le_mul_right (w r) (hfiber r hr)
    _ = _ := Cauchy.sumBelow_mul_left q mu w

/-- The complete finite incidence inequality: `families` many same-fiber
relations supply the lower bound, overlap weights supply the upper bound.

`bins` is the number of cosets for each sign choice; `q` is the number of exact
distance labels. They are different quantities and are not identified here. -/
theorem fiber_weighted_sieve (families n bins q : Nat) (A : Nat → Bool)
    (coset : Nat → Nat → Nat) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (w : Nat → Nat) (mu : Nat)
    (hcoset : ∀ e, e < families → ∀ i, i < n → A i = true → coset e i < bins)
    (hsize : 2 * bins ≤ countBelow n A)
    (hinclude : ∀ e, e < families → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (coset e) i j = true → eligible i j = true)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → label i j < q)
    (hoverlap : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      overlap families (fun e => Fibers.sameFiber A (coset e)) i j ≤ w (label i j))
    (hfiber : ∀ r, r < q → pairFiber n eligible label r ≤ mu) :
    families * (countBelow n A) ^ 2 ≤
      2 * bins * (mu * sumBelow q w) := by
  have hlo : sumBelow families (fun _ => (countBelow n A) ^ 2) ≤
      sumBelow families (fun e => 2 * bins * pairCount n (Fibers.sameFiber A (coset e))) := by
    apply sumBelow_le
    intro e he
    exact same_fiber_lower n bins A (coset e) (hcoset e he) hsize
  rw [Cauchy.sumBelow_const, Cauchy.sumBelow_mul_left] at hlo
  have hhi := weighted_overlap_bound families n q
    (fun e => Fibers.sameFiber A (coset e)) eligible label w mu
    hinclude hlabel hoverlap hfiber
  exact Nat.le_trans hlo (Nat.mul_le_mul_left (2 * bins) hhi)

end JSP1012.Sieve

#print axioms JSP1012.Sieve.family_incidence
#print axioms JSP1012.Sieve.pair_weight_partition
#print axioms JSP1012.Sieve.weighted_overlap_bound
#print axioms JSP1012.Sieve.fiber_weighted_sieve
