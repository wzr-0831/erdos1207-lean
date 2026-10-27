import WeightedOverlap

/-!
# Applying the finite weighted sieve to isosceles-free subsets

This is the finite end of the EP1207 / LPZ26 argument, not its missing geometric
construction. It derives exclusion of isosceles-free subsets from explicit
coset labels, explicit overlap weights, and a numerical mass inequality. It
never asserts that such data exist for arbitrary large planar point sets.
-/

namespace JSP1012.Application
open JSP1012

/-- Eligible pairs form a genuine subset of the selected, distinct vertex pairs. -/
def EligibleSelected (n : Nat) (A : Nat → Bool) (eligible : Nat → Nat → Bool) : Prop :=
  ∀ i, i < n → ∀ j, j < n → eligible i j = true →
    A i = true ∧ A j = true ∧ i ≠ j

/-- A distance fiber of an eligible subrelation cannot exceed the full selected
ordered-pair multiplicity. This verifies the upper bound required by the sieve. -/
theorem pairFiber_le_distanceMultiplicity {n : Nat} {A : Nat → Bool}
    {eligible : Nat → Nat → Bool} {d : Nat → Nat → Nat}
    (heligible : EligibleSelected n A eligible) (r : Nat) :
    Sieve.pairFiber n eligible d r ≤ distanceMultiplicity n A d r := by
  apply pairCount_mono
  intro i hi j hj hpair
  have hd : eligible i j = true ∧ d i j = r := by
    simpa [Bool.and_eq_true] using hpair
  obtain ⟨hai, haj, hij⟩ := heligible i hi j hj hd.1
  simp [restrictRelation, distanceRelation, hai, haj, hij, hd.2]

/-- Explicit finite sieve data force a repeated distance from one apex as soon
as their mass exceeds the maximum possible for an isosceles-free subset. -/
theorem weighted_sieve_excludes_free (families n bins q : Nat) (A : Nat → Bool)
    (coset : Nat → Nat → Nat) (eligible : Nat → Nat → Bool)
    (d : Nat → Nat → Nat) (w : Nat → Nat)
    (hcoset : ∀ e, e < families → ∀ i, i < n → A i = true → coset e i < bins)
    (hsize : 2 * bins ≤ countBelow n A)
    (hinclude : ∀ e, e < families → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (coset e) i j = true → eligible i j = true)
    (heligible : EligibleSelected n A eligible)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → d i j < q)
    (hoverlap : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      Sieve.overlap families (fun e => Fibers.sameFiber A (coset e)) i j ≤ w (d i j))
    (hmass : 2 * bins * sumBelow q w < families * countBelow n A) :
    ¬ IsoscelesFree n A d := by
  intro hfree
  have hfiber : ∀ r, r < q → Sieve.pairFiber n eligible d r ≤ countBelow n A := by
    intro r hr
    exact Nat.le_trans (pairFiber_le_distanceMultiplicity heligible r)
      (distanceMultiplicity_le_card hfree r)
  have hsieve := Sieve.fiber_weighted_sieve families n bins q A coset eligible d w
    (countBelow n A) hcoset hsize hinclude hlabel hoverlap hfiber
  have hpos : 0 < countBelow n A := by
    by_cases hz : countBelow n A = 0
    · simp [hz] at hmass
    · omega
  have hstrict := Nat.mul_lt_mul_of_pos_left hmass hpos
  have hleft : families * countBelow n A ^ 2 =
      countBelow n A * (families * countBelow n A) := by grind
  have hright : 2 * bins * (countBelow n A * sumBelow q w) =
      countBelow n A * (2 * bins * sumBelow q w) := by grind
  rw [hleft, hright] at hsieve
  omega

/-- The negation above really supplies three distinct selected vertices and an
equal-distance wedge; degenerate collinear isosceles triples are not excluded. -/
theorem equal_label_wedge_of_not_free {n : Nat} {A : Nat → Bool}
    {d : Nat → Nat → Nat} (h : ¬ IsoscelesFree n A d) :
    ∃ i, i < n ∧ A i = true ∧ ∃ j, j < n ∧ A j = true ∧
      ∃ k, k < n ∧ A k = true ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ d i j = d i k := by
  classical
  by_cases hw : ∃ i, i < n ∧ A i = true ∧ ∃ j, j < n ∧ A j = true ∧
      ∃ k, k < n ∧ A k = true ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ d i j = d i k
  · exact hw
  · apply False.elim
    apply h
    intro i hi hai j hj haj k hk hak hij hik hjk heq
    exact hw ⟨i, hi, hai, j, hj, haj, k, hk, hak, hij, hik, hjk, heq⟩

end JSP1012.Application

#print axioms JSP1012.Application.pairFiber_le_distanceMultiplicity
#print axioms JSP1012.Application.weighted_sieve_excludes_free
#print axioms JSP1012.Application.equal_label_wedge_of_not_free
