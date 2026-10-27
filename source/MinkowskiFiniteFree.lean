import MinkowskiPairData
import SetIsoscelesBridge
import FreeSetMass

/-!
# Actual finite free-subset bound in a split-field Minkowski grid

Source preparation. This composes actual residue data, actual candidate-box
counts and actual Euclidean freeness. There is no assumed Cauchy inequality,
CRT cardinality, overlap bound, lattice count or robust-distance theorem.

This is NOT yet EP1207: an unbounded-degree uniformly bounded-discriminant
split-field input and the final parameter/asymptotic construction remain.
-/

noncomputable section

namespace JSP1012.MinkowskiFiniteFree

open NumberField NumberFieldBox BoxGridConstruction MinkowskiResidueFamily
open MinkowskiPairData
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- Every genuinely isosceles-free actual subset of the Minkowski grid satisfies
the finite LPZ mass inequality. Freeness has the EXACT expanded FC semantics. -/
theorem free_set_mass (f : SplitFamily K) (w : InfinitePlace K)
    (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ) (hm : 1 ≤ m)
    (hd : 0 < Module.finrank ℚ K)
    (hA : A ⊆ (boxFinset K ((Q f * m : ℕ) : ℝ)) ×ˢ
      (boxFinset K ((Q f * m : ℕ) : ℝ)))
    (hlarge : 2 * Q f ^ Module.finrank ℚ K ≤ A.card)
    (hfree : SetIsoscelesBridge.NoIsosceles
      (↑(A.image (planarPoint w)) : Set (EuclideanSpace ℝ (Fin 2)))) :
    2 ^ k f * A.card ≤ 2 * Q f ^ Module.finrank ℚ K *
      (17 * m ^ 2 * (f.ps.map (fun p => p + 1)).prod) ^ Module.finrank ℚ K := by
  have hco : ((idealList f).toFinset : Set (Ideal (𝓞 K))).Pairwise IsCoprime := by
    simpa only [MinkowskiResidueFamily.idealSet] using MinkowskiResidueFamily.pairwise_coprime f
  have hfreeIndexed : IsoscelesFree A.card (fun _ => true) (trueDistance w A) :=
    SetIsoscelesBridge.indexed_planar_free_of_image_noIsosceles w A (0, 0) hfree
  have hmass : 2 ^ k f * countBelow A.card (fun _ => true) ≤
      2 * (radixList f).prod * sumBelow (2 ^ k f)
        (CandidateWeights.subsetBound (idealList f) (Q f) m) := by
    apply FreeSetMass.finite_sieve_free_mass A.card (k f)
      (CandidateWeights.candidates (K := K) (Q f) m).card (fun _ => true)
      (radixList f) (residues f A) (eligible f A m) (finiteLabel f A m)
      (trueDistance w A) (signData f A)
      (CandidateWeights.squareBits (idealList f) (Q f) m)
      (CandidateWeights.subsetBound (idealList f) (Q f) m)
    · intro e he i hi hai
      exact residue_bounded f A he i
    · rw [FinsetEnumeration.countBelow_true A, radixList_product]
      exact hlarge
    · intro e he i hi j hj hpair
      exact eligible_of_sameFiber f A m hA he hi hj hpair
    · exact eligible_selected f A m
    · exact respectsAtApex f w A m
    · intro i hi j hj hE
      exact label_lt_of_eligible f A m hE
    · intro i hi j hj hE
      exact signData_length f A i j
    · intro e he i hi j hj hpair
      exact compatible_of_sameFiber f A he hpair
    · intro i hi j hj hE
      exact bothCount_le_bits f A m hE
    · intro r hr
      exact squareBits_length f m r
    · intro e he
      have h := CandidateWeights.subset_count_le (idealList f) (idealList_nodup f) hco
        (Q f) m (idealList_product f) e (by simpa only [idealList_length] using he)
      simpa only [CandidateWeights.wordAt, idealList_length] using h
    · exact hfreeIndexed
  rw [FinsetEnumeration.countBelow_true A, radixList_product] at hmass
  have hsum := CandidateWeights.total_subsetBound_le (idealList f) f.ps
    (fun p hp => (f.prime p hp).pos) (idealList_norms f) m hm hd
  rw [idealList_length] at hsum
  exact hmass.trans (Nat.mul_le_mul_left (2 * Q f ^ Module.finrank ℚ K) hsum)

/-- Row-major k=d*|ps| gives the exact family amplification power. -/
theorem sign_family_power (f : SplitFamily K) :
    2 ^ k f = (2 ^ f.ps.length) ^ Module.finrank ℚ K := by
  rw [k_eq, Nat.mul_comm (Module.finrank ℚ K) f.ps.length, Nat.pow_mul]

/-- Denominator-cleared form consumed by the separately proved integer mass
cancellation. The complete candidate-count assumptions have been discharged. -/
theorem free_set_scaled_mass (f : SplitFamily K) (w : InfinitePlace K)
    (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ) (hm : 1 ≤ m)
    (hd : 0 < Module.finrank ℚ K)
    (hA : A ⊆ (boxFinset K ((Q f * m : ℕ) : ℝ)) ×ˢ
      (boxFinset K ((Q f * m : ℕ) : ℝ)))
    (hlarge : 2 * Q f ^ Module.finrank ℚ K ≤ A.card)
    (hfree : SetIsoscelesBridge.NoIsosceles
      (↑(A.image (planarPoint w)) : Set (EuclideanSpace ℝ (Fin 2)))) :
    (2 ^ f.ps.length) ^ Module.finrank ℚ K * A.card ≤
      2 * Q f ^ Module.finrank ℚ K *
        ((17 * (f.ps.map (fun p => p + 1)).prod) * m ^ 2) ^ Module.finrank ℚ K := by
  have h := free_set_mass f w A m hm hd hA hlarge hfree
  rw [sign_family_power] at h
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

end JSP1012.MinkowskiFiniteFree

#print axioms JSP1012.MinkowskiFiniteFree.free_set_mass
#print axioms JSP1012.MinkowskiFiniteFree.free_set_scaled_mass
