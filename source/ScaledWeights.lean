import SubsetWeights

/-!
# Exact scaled occurrence-divisor weights in Nat

For integer box radius X=Q*m, the LPZ lattice upper bound has numerator
(c*Q)^d with c=17*m^2, and every occurrence-subset norm divides Q^d.
Consequently all divisions are EXACT natural divisions. This file proves the
scaled aggregate identity and its use for actual finite lists of candidate
counts. The ideal/norm interpretation remains an explicit separate obligation.
-/

namespace JSP1012.ScaledWeights
open JSP1012

private theorem sum_map_mul {α : Type} (xs : List α) (f : α → Nat) (c : Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ a, a ∈ xs → f a ≤ g a) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    apply Nat.add_le_add (h x (by simp))
    exact ih (fun a ha => h a (by simp [ha]))

/-- Exact denominator clearing for an integer multiple of the common norm.
Repeated equal norms retain occurrence multiplicity throughout. -/
theorem scaled_reciprocal_subset_sum (d c : Nat) (ps : List Nat)
    (hpos : ∀ p, p ∈ ps → 0 < p) :
    ((Weights.subsetProducts (Weights.repeatedNorms d ps)).map
      (fun a => (c * ps.prod) ^ d / a)).sum =
        (c * (ps.map (fun p => p + 1)).prod) ^ d := by
  have hm : (Weights.subsetProducts (Weights.repeatedNorms d ps)).map
      (fun a => (c * ps.prod) ^ d / a) =
      (Weights.subsetProducts (Weights.repeatedNorms d ps)).map
        (fun a => c ^ d * (ps.prod ^ d / a)) := by
    apply List.map_congr_left
    intro a ha
    have hdvd : a ∣ ps.prod ^ d := by
      have h := Weights.subsetProduct_dvd (Weights.repeatedNorms d ps) a ha
      rw [Weights.repeatedNorms_product] at h
      exact h
    rw [Nat.mul_pow]
    exact Nat.mul_div_assoc (c ^ d) hdvd
  rw [hm, sum_map_mul, Weights.repeated_reciprocal_subset_sum d ps hpos, ← Nat.mul_pow]

/-- An actual list of ideal-divisor candidates may be used after its norm list
is identified with the occurrence-subset enumeration. Equal numerical norms
are NOT deduplicated and candidate counts are NOT identified merely by norm. -/
theorem aggregate_counts_le {α : Type} (entries : List α) (norm count : α → Nat)
    (d c : Nat) (ps : List Nat) (hpos : ∀ p, p ∈ ps → 0 < p)
    (hnorms : entries.map norm = Weights.subsetProducts (Weights.repeatedNorms d ps))
    (hcount : ∀ a, a ∈ entries → count a ≤ (c * ps.prod) ^ d / norm a) :
    (entries.map count).sum ≤ (c * (ps.map (fun p => p + 1)).prod) ^ d := by
  have h := sum_map_le entries count (fun a => (c * ps.prod) ^ d / norm a) hcount
  have heq : (entries.map norm).map (fun a => (c * ps.prod) ^ d / a) =
      entries.map (fun a => (c * ps.prod) ^ d / norm a) := by
    simp only [List.map_map, Function.comp_def]
  rw [← heq, hnorms, scaled_reciprocal_subset_sum d c ps hpos] at h
  exact h

end JSP1012.ScaledWeights

#print axioms JSP1012.ScaledWeights.scaled_reciprocal_subset_sum
#print axioms JSP1012.ScaledWeights.aggregate_counts_le
