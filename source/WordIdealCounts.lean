import IdealWordProducts
import IntegerIdealCounts
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Actual lattice counts summed over all coordinate occurrence words

Source preparation. Counts are ACTUAL ideal-box cardinalities, not assumed
count functions. Every Boolean word is retained even when its product/norm
coincides with another word's. The norm-list identification remains the exact
interface already constructed by PrimeCoordinateLists.coordinates_norm_list.
-/

noncomputable section

namespace JSP1012.WordIdealCounts

open NumberField NumberFieldBox

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- The actual candidate box for one actual extra ideal factor. -/
def count (Q m : ℕ) (J : Ideal (𝓞 K)) : ℕ :=
  (idealBoxFinset (Ideal.span {(Q : 𝓞 K)} * J)
    (8 * ((Q * m : ℕ) : ℝ) ^ 2)).card

/-- Each actual occurrence word has the required exact integer upper bound.
Its norm positivity and upper bound are DERIVED from the actual norm list. -/
theorem count_le (Is : List (Ideal (𝓞 K))) (ps : List ℕ)
    (hpositive : ∀ p ∈ ps, 0 < p)
    (hnorms : Is.map Ideal.absNorm = Weights.repeatedNorms (Module.finrank ℚ K) ps)
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < Module.finrank ℚ K)
    (J : Ideal (𝓞 K)) (hJ : J ∈ IdealWordProducts.wordProducts Is) :
    count ps.prod m J ≤ (17 * m ^ 2 * ps.prod) ^ Module.finrank ℚ K / J.absNorm := by
  have hQ : 0 < ps.prod := List.prod_pos hpositive
  have hQpow : 0 < ps.prod ^ Module.finrank ℚ K := Nat.pow_pos hQ
  have hJnorm : J.absNorm ∈ Weights.subsetProducts
      (Weights.repeatedNorms (Module.finrank ℚ K) ps) := by
    rw [← hnorms, ← IdealWordProducts.wordProducts_norm_list]
    exact List.mem_map.mpr ⟨J, hJ, rfl⟩
  have hdvd := Weights.subsetProduct_dvd
    (Weights.repeatedNorms (Module.finrank ℚ K) ps) J.absNorm hJnorm
  rw [Weights.repeatedNorms_product] at hdvd
  have hJpos : 0 < J.absNorm := Nat.pos_of_dvd_of_pos hdvd hQpow
  have hJle : J.absNorm ≤ ps.prod ^ Module.finrank ℚ K := Nat.le_of_dvd hQpow hdvd
  have hnorm : (Ideal.span {(ps.prod : 𝓞 K)} * J).absNorm =
      ps.prod ^ Module.finrank ℚ K * J.absNorm := by
    rw [map_mul, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hnonzero : Ideal.span {(ps.prod : 𝓞 K)} * J ≠ ⊥ := by
    intro hz
    have hpos : 0 < (Ideal.span {(ps.prod : 𝓞 K)} * J).absNorm := by
      rw [hnorm]
      exact Nat.mul_pos hQpow hJpos
    rw [hz, Ideal.absNorm_bot] at hpos
    omega
  simpa only [count, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    IntegerIdealCounts.idealBox_card_le_div
      (Ideal.span {(ps.prod : 𝓞 K)} * J) hnonzero ps.prod m J.absNorm
      hQ hm hJpos hd hnorm hJle

/-- The complete finite candidate mass upper bound, using actual boxes and
retaining all coordinate-word multiplicities. No abstract lattice-count
hypothesis survives in this theorem. -/
theorem total_count_le (Is : List (Ideal (𝓞 K))) (ps : List ℕ)
    (hpositive : ∀ p ∈ ps, 0 < p)
    (hnorms : Is.map Ideal.absNorm = Weights.repeatedNorms (Module.finrank ℚ K) ps)
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < Module.finrank ℚ K) :
    ((IdealWordProducts.wordProducts Is).map (count ps.prod m)).sum ≤
      (17 * m ^ 2 * (ps.map (fun p => p + 1)).prod) ^ Module.finrank ℚ K := by
  apply IdealWordProducts.aggregate_wordProduct_counts_le
    Is (count ps.prod m) (Module.finrank ℚ K) (17 * m ^ 2) ps hpositive hnorms
  intro J hJ
  exact count_le Is ps hpositive hnorms m hm hd J hJ

end JSP1012.WordIdealCounts

#print axioms JSP1012.WordIdealCounts.count_le
#print axioms JSP1012.WordIdealCounts.total_count_le
