import MinkowskiResidueFamily
import CandidateWeights
import SquaredDistanceBox
import FinsetEnumeration

/-!
# Actual point, residue and candidate data for the finite sieve

Source preparation. All vertices are actual elements of A; all residues use
the one fixed coordinate-data list. Eligible pairs have their integral squared
distance in the actual candidate ideal box. Default labels are NEVER asserted
injective outside eligible pairs. Both point and sign-word prefix guards are
retained. This module supplies finite-certificate hypotheses, not a tower.
-/

noncomputable section

namespace JSP1012.MinkowskiPairData

open NumberField NumberFieldBox NumberFieldCoordinates BoxGridConstruction
open MinkowskiResidueFamily SignedResidueVectors
open scoped BigOperators Classical

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

def vertex (A : Finset (𝓞 K × 𝓞 K)) (i : ℕ) : 𝓞 K × 𝓞 K :=
  FinsetEnumeration.pointAt A (0, 0) i

def normLabel (A : Finset (𝓞 K × 𝓞 K)) (i j : ℕ) : 𝓞 K :=
  SquaredDistanceBox.squaredDifference (vertex A i) (vertex A j)

def eligible (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m i j : ℕ) : Bool :=
  decide (i ≠ j ∧ normLabel A i j ∈ CandidateWeights.candidates (Q f) m)

def finiteLabel (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m i j : ℕ) : ℕ :=
  FinsetEnumeration.index (CandidateWeights.candidates (Q f) m) (normLabel A i j)

def trueDistance (w : InfinitePlace K) (A : Finset (𝓞 K × 𝓞 K)) (i j : ℕ) : ℝ :=
  dist (planarPoint w (vertex A i)) (planarPoint w (vertex A j))

def residues (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (e i : ℕ) : List ℕ :=
  digits (quotientCoordinates f) (word f e) (vertex A i).1 (vertex A i).2

def signData (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (i j : ℕ) : List (Bool × Bool) :=
  signPermissions (quotientCoordinates f)
    ((vertex A i).1 - (vertex A j).1) ((vertex A i).2 - (vertex A j).2)

theorem residue_bounded (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K))
    {e : ℕ} (he : e < 2 ^ k f) (i : ℕ) :
    Radix.Bounded (radixList f) (residues f A e i) :=
  MinkowskiResidueFamily.digits_bounded f he _ _

theorem eligible_selected (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ) :
    Application.EligibleSelected A.card (fun _ => true) (eligible f A m) := by
  intro i hi j hj hE
  have hparts : i ≠ j ∧ normLabel A i j ∈ CandidateWeights.candidates (Q f) m :=
    of_decide_eq_true hE
  exact ⟨rfl, rfl, hparts.1⟩

theorem label_lt_of_eligible (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ)
    {i j : ℕ} (hE : eligible f A m i j = true) :
    finiteLabel f A m i j < (CandidateWeights.candidates (K := K) (Q f) m).card := by
  have hparts : i ≠ j ∧ normLabel A i j ∈ CandidateWeights.candidates (Q f) m :=
    of_decide_eq_true hE
  exact FinsetEnumeration.index_lt _ hparts.2

/-- Equal ELIGIBLE candidate labels preserve the genuine Euclidean distances. -/
theorem respectsAtApex (f : SplitFamily K) (w : InfinitePlace K)
    (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ) :
    TrueDistances.RespectsAtApex A.card (eligible f A m) (finiteLabel f A m) (trueDistance w A) := by
  intro i hi j hj l hl hEij hEil heq
  have hij : i ≠ j ∧ normLabel A i j ∈ CandidateWeights.candidates (Q f) m :=
    of_decide_eq_true hEij
  have hil : i ≠ l ∧ normLabel A i l ∈ CandidateWeights.candidates (Q f) m :=
    of_decide_eq_true hEil
  have hnorm := FinsetEnumeration.index_injective_on_members
    (CandidateWeights.candidates (Q f) m) hij.2 hil.2 heq
  exact dist_eq_of_sqLabel_eq w (vertex A i) (vertex A j) (vertex A l) hnorm

theorem signData_length (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (i j : ℕ) :
    (signData f A i j).length = k f := by
  simp only [signData, signPermissions_length, quotientCoordinates, List.length_map, k]

theorem squareBits_length (f : SplitFamily K) (m r : ℕ) :
    (CandidateWeights.squareBits (idealList f) (Q f) m r).length = k f := by
  simp only [CandidateWeights.squareBits, IdealWordMembership.squareBits, List.length_map,
    idealList_length]

/-- Same finite residue fiber means actual same-r sign compatibility. -/
theorem compatible_of_sameFiber (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K))
    {e i j : ℕ} (he : e < 2 ^ k f)
    (hf : Fibers.sameFiber (fun _ => true)
      (fun a => Radix.encode (radixList f) (residues f A e a)) i j = true) :
    SignOverlap.compatible (signData f A i j) (word f e) = true := by
  have hparts : i ≠ j ∧
      Radix.encode (radixList f) (residues f A e i) =
        Radix.encode (radixList f) (residues f A e j) := by
    simpa only [Fibers.sameFiber, Bool.true_and, decide_eq_true_eq] using hf
  apply (SignedResidueVectors.label_eq_iff_compatible (quotientCoordinates f) (word f e)
    (by simpa only [quotientCoordinates, List.length_map, k] using word_length f he)
    (vertex A i).1 (vertex A i).2 (vertex A j).1 (vertex A j).2).mp
  exact hparts.2

/-- Decode only an ACTUAL candidate member. The fallback index is not global. -/
theorem candidateAt_label (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ)
    {i j : ℕ} (hE : eligible f A m i j = true) :
    CandidateWeights.candidateAt (Q f) m (finiteLabel f A m i j) = normLabel A i j := by
  have hparts : i ≠ j ∧ normLabel A i j ∈ CandidateWeights.candidates (Q f) m :=
    of_decide_eq_true hE
  exact FinsetEnumeration.pointAt_index _ 0 hparts.2

theorem bothCount_le_bits (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ)
    {i j : ℕ} (hE : eligible f A m i j = true) :
    SignOverlap.bothCount (signData f A i j) ≤
      (CandidateWeights.squareBits (idealList f) (Q f) m (finiteLabel f A m i j)).countP id := by
  have h := LocalSignArithmetic.bothCount_le_square_count (coordinateData f)
    ((vertex A i).1 - (vertex A j).1) ((vertex A i).2 - (vertex A j).2)
  have hbase : SignOverlap.bothCount (signData f A i j) ≤
      (LocalSignArithmetic.squareBits (coordinateData f) (normLabel A i j)).countP id := by
    simpa only [LocalSignArithmetic.baseCoordinates, signData, quotientCoordinates,
      normLabel, SquaredDistanceBox.squaredDifference] using h
  have hbits : LocalSignArithmetic.squareBits (coordinateData f) (normLabel A i j) =
      IdealWordMembership.squareBits (idealList f) (normLabel A i j) := by
    simp only [LocalSignArithmetic.squareBits, IdealWordMembership.squareBits, idealList,
      List.map_map, Function.comp_def]
  rw [hbits] at hbase
  rw [CandidateWeights.squareBits, candidateAt_label f A m hE]
  exact hbase

/-- The ACTUAL ideal product, not an assumed complete-splitting factorization. -/
theorem coordinate_product_eq (f : SplitFamily K) :
    (∏ I ∈ LocalSignArithmetic.idealSet (coordinateData f), I) = Ideal.span {(Q f : 𝓞 K)} := by
  have hlist : (∏ I ∈ LocalSignArithmetic.idealSet (coordinateData f), I) = (idealList f).prod := by
    simpa only [LocalSignArithmetic.idealSet, LocalSignArithmetic.ideals, idealList,
      List.map_id, id_eq] using List.prod_toFinset id (idealList_nodup f)
  exact hlist.trans (idealList_product f)

/-- Actual common residue fibers are included among actual candidate pairs.
The radius8X² bound comes from the proved integral squared-distance box lemma. -/
theorem eligible_of_sameFiber (f : SplitFamily K) (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ)
    (hA : A ⊆ (boxFinset K ((Q f * m : ℕ) : ℝ)) ×ˢ
      (boxFinset K ((Q f * m : ℕ) : ℝ)))
    {e i j : ℕ} (he : e < 2 ^ k f) (hi : i < A.card) (hj : j < A.card)
    (hf : Fibers.sameFiber (fun _ => true)
      (fun a => Radix.encode (radixList f) (residues f A e a)) i j = true) :
    eligible f A m i j = true := by
  have hparts : i ≠ j ∧
      Radix.encode (radixList f) (residues f A e i) =
        Radix.encode (radixList f) (residues f A e j) := by
    simpa only [Fibers.sameFiber, Bool.true_and, decide_eq_true_eq] using hf
  have hco : (LocalSignArithmetic.idealSet (coordinateData f) : Set (Ideal (𝓞 K))).Pairwise
      IsCoprime := pairwise_coprime f
  have hnorm := LocalSignArithmetic.norm_mem_product_of_compatible (coordinateData f) hco
    (word f e) (word_length f he) ((vertex A i).1 - (vertex A j).1)
    ((vertex A i).2 - (vertex A j).2) (compatible_of_sameFiber f A he hf)
  rw [coordinate_product_eq f] at hnorm
  have hzbox := SquaredDistanceBox.squaredDifference_mem_box
    (show (0 : ℝ) ≤ ((Q f * m : ℕ) : ℝ) by positivity)
    (hA (FinsetEnumeration.pointAt_mem A (0, 0) hi))
    (hA (FinsetEnumeration.pointAt_mem A (0, 0) hj))
  apply decide_eq_true
  exact ⟨hparts.1, (mem_idealBoxFinset _ _ _).mpr
    ⟨hnorm, (mem_boxFinset _ _).mp hzbox⟩⟩

/-- Bounded distinct eligible indices have a genuinely nonzero integral label.
The candidate set may contain zero; it is never the label of such a pair. -/
theorem eligible_normLabel_ne_zero (f : SplitFamily K) (w : InfinitePlace K)
    (A : Finset (𝓞 K × 𝓞 K)) (m : ℕ) {i j : ℕ}
    (hi : i < A.card) (hj : j < A.card) (hE : eligible f A m i j = true) :
    normLabel A i j ≠ 0 := by
  have hparts : i ≠ j ∧ normLabel A i j ∈ CandidateWeights.candidates (Q f) m :=
    of_decide_eq_true hE
  have hxy : vertex A i ≠ vertex A j := by
    intro heq
    exact hparts.1 (FinsetEnumeration.pointAt_injective A (0, 0) hi hj heq)
  exact SquaredDistanceBox.squaredDifference_ne_zero w hxy

end JSP1012.MinkowskiPairData

#print axioms JSP1012.MinkowskiPairData.respectsAtApex
#print axioms JSP1012.MinkowskiPairData.compatible_of_sameFiber
#print axioms JSP1012.MinkowskiPairData.bothCount_le_bits
#print axioms JSP1012.MinkowskiPairData.eligible_of_sameFiber

#print axioms JSP1012.MinkowskiPairData.eligible_normLabel_ne_zero
