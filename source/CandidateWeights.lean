import IdealWordMembership
import WordIdealCounts
import FinsetEnumeration
import FreeSetMass
import Mathlib.Data.List.GetD

/-!
# Actual candidate-filter bounds and total candidate weight

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.


Candidates are the ACTUAL finite ideal box for `(Q)` at radius `8*(Q*m)^2`.
A valid sign-word index selects an ACTUAL word from the proved complete
signWords enumeration. The word-length and membership lemmas retain the bound
`e < 2^Is.length`; no global fallback-label injectivity is asserted.

The subset-count upper bound is DERIVED by identifying indexed counting with
an actual filtered candidate finset and including that finset in the actual
`(Q)*wordProduct` ideal box. The total mass upper bound is then DERIVED from
the actual WordIdealCounts theorem and the actual sign-word sum identity.
No abstract hcount/lattice-count hypothesis is introduced.
-/

noncomputable section

namespace JSP1012.CandidateWeights

open NumberField NumberFieldBox
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- The actual full candidate ideal box. -/
def candidates (Q m : ℕ) : Finset (𝓞 K) :=
  idealBoxFinset (Ideal.span {(Q : 𝓞 K)}) (8 * ((Q * m : ℕ) : ℝ) ^ 2)

/-- The default value is used only outside the actual finite candidate prefix. -/
def candidateAt (Q m r : ℕ) : 𝓞 K :=
  FinsetEnumeration.pointAt (candidates Q m) 0 r

/-- Actual candidate square-membership bits, with no assumed ideal divisibility. -/
def squareBits (Is : List (Ideal (𝓞 K))) (Q m r : ℕ) : List Bool :=
  IdealWordMembership.squareBits Is (candidateAt Q m r)

/-- Actual indexed sign word; public word lemmas require a valid finite index. -/
def wordAt (Is : List (Ideal (𝓞 K))) (e : ℕ) : List Bool :=
  (SignOverlap.signWords Is.length).getD e []

/-- The actual ideal-box count for this word's extra ideal product. -/
def subsetBound (Is : List (Ideal (𝓞 K))) (Q m e : ℕ) : ℕ :=
  WordIdealCounts.count Q m (IdealWordProducts.wordProduct Is (wordAt Is e))

/-- The actual finite candidate list filtered by actual allowed square subsets. -/
def allowedCandidates (Is : List (Ideal (𝓞 K))) (Q m : ℕ) (word : List Bool) : Finset (𝓞 K) :=
  (candidates Q m).filter (fun z =>
    DivisorIncidence.subsetAllowed (IdealWordMembership.squareBits Is z) word = true)

theorem candidateAt_mem (Q m : ℕ) {r : ℕ} (hr : r < (candidates (K := K) Q m).card) :
    candidateAt (K := K) Q m r ∈ candidates Q m :=
  FinsetEnumeration.pointAt_mem (candidates Q m) 0 hr

/-- The complete word enumeration supplies an ACTUAL full word at every valid index. -/
theorem wordAt_mem (Is : List (Ideal (𝓞 K))) (e : ℕ) (he : e < 2 ^ Is.length) :
    wordAt Is e ∈ SignOverlap.signWords Is.length := by
  have hi : e < (SignOverlap.signWords Is.length).length := by
    rw [SignOverlap.signWords_length]
    exact he
  unfold wordAt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem wordAt_length (Is : List (Ideal (𝓞 K))) (e : ℕ) (he : e < 2 ^ Is.length) :
    (wordAt Is e).length = Is.length :=
  (SignOverlap.mem_signWords_iff Is.length (wordAt Is e)).mp (wordAt_mem Is e he)

/-- Actual indexed counting is exactly the cardinality of the actual filter.
This is an equality, not an assumed enumeration/cardinality correspondence. -/
theorem countBelow_eq_allowed_card (Is : List (Ideal (𝓞 K))) (Q m : ℕ) (word : List Bool) :
    countBelow (candidates (K := K) Q m).card
      (fun r => DivisorIncidence.subsetAllowed (squareBits Is Q m r) word) =
        (allowedCandidates Is Q m word).card := by
  classical
  have h := FinsetEnumeration.countBelow_eq_filter_card (candidates (K := K) Q m) 0
    (fun z => DivisorIncidence.subsetAllowed (IdealWordMembership.squareBits Is z) word = true)
  simpa only [squareBits, candidateAt, allowedCandidates, Bool.decide_eq_true] using h

/-- Every actually allowed candidate lies in the actual extra-factor ideal box,
with exactly the SAME coordinate box bound, not a numerically assumed bound. -/
theorem allowedCandidates_subset_extra (Is : List (Ideal (𝓞 K))) (hIs : Is.Nodup)
    (hcoprime : (Is.toFinset : Set (Ideal (𝓞 K))).Pairwise IsCoprime)
    (Q m : ℕ) (hprod : Is.prod = Ideal.span {(Q : 𝓞 K)})
    (word : List Bool) (hlen : word.length = Is.length) :
    allowedCandidates Is Q m word ⊆
      idealBoxFinset (Ideal.span {(Q : 𝓞 K)} * IdealWordProducts.wordProduct Is word)
        (8 * ((Q * m : ℕ) : ℝ) ^ 2) := by
  classical
  intro z hz
  have hselected : z ∈ candidates Q m ∧
      DivisorIncidence.subsetAllowed (IdealWordMembership.squareBits Is z) word = true :=
    Finset.mem_filter.mp hz
  have hzbox := (mem_idealBoxFinset (Ideal.span {(Q : 𝓞 K)})
    (8 * ((Q * m : ℕ) : ℝ) ^ 2) z).mp hselected.1
  have hzprod : z ∈ Is.prod := by rw [hprod]; exact hzbox.1
  have hextra := IdealWordMembership.mem_product_mul_wordProduct
    Is word hlen hIs hcoprime z hzprod hselected.2
  apply (mem_idealBoxFinset _ _ z).mpr
  exact ⟨by simpa only [hprod] using hextra, hzbox.2⟩

/-- Actual candidate subset counts have the actual ideal-box count upper bound.
The sign-word index restriction is retained explicitly. -/
theorem subset_count_le (Is : List (Ideal (𝓞 K))) (hIs : Is.Nodup)
    (hcoprime : (Is.toFinset : Set (Ideal (𝓞 K))).Pairwise IsCoprime)
    (Q m : ℕ) (hprod : Is.prod = Ideal.span {(Q : 𝓞 K)})
    (e : ℕ) (he : e < 2 ^ Is.length) :
    countBelow (candidates (K := K) Q m).card
      (fun r => DivisorIncidence.subsetAllowed (squareBits Is Q m r) (wordAt Is e)) ≤
        subsetBound Is Q m e := by
  calc
    _ = (allowedCandidates Is Q m (wordAt Is e)).card :=
      countBelow_eq_allowed_card Is Q m (wordAt Is e)
    _ ≤ (idealBoxFinset
        (Ideal.span {(Q : 𝓞 K)} * IdealWordProducts.wordProduct Is (wordAt Is e))
        (8 * ((Q * m : ℕ) : ℝ) ^ 2)).card :=
      Finset.card_le_card
        (allowedCandidates_subset_extra Is hIs hcoprime Q m hprod (wordAt Is e) (wordAt_length Is e he))
    _ = subsetBound Is Q m e := rfl

/-- Actual indexed subset bounds sum to exactly the actual occurrence-word
ideal counts, including every multiplicity. -/
theorem sum_subsetBound_eq (Is : List (Ideal (𝓞 K))) (Q m : ℕ) :
    sumBelow (2 ^ Is.length) (subsetBound Is Q m) =
      ((IdealWordProducts.wordProducts Is).map (WordIdealCounts.count Q m)).sum := by
  calc
    _ = ((SignOverlap.signWords Is.length).map
        (fun word => WordIdealCounts.count Q m (IdealWordProducts.wordProduct Is word))).sum :=
      FreeSetMass.sumBelow_signWords Is.length
        (fun word => WordIdealCounts.count Q m (IdealWordProducts.wordProduct Is word))
    _ = _ := by simp only [IdealWordProducts.wordProducts, List.map_map, Function.comp_def]

/-- The total ACTUAL candidate weight is bounded without an hcount assumption. -/
theorem total_subsetBound_le (Is : List (Ideal (𝓞 K))) (ps : List ℕ)
    (hpositive : ∀ p ∈ ps, 0 < p)
    (hnorms : Is.map Ideal.absNorm = Weights.repeatedNorms (Module.finrank ℚ K) ps)
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < Module.finrank ℚ K) :
    sumBelow (2 ^ Is.length) (subsetBound Is ps.prod m) ≤
      (17 * m ^ 2 * (ps.map (fun p => p + 1)).prod) ^ Module.finrank ℚ K := by
  rw [sum_subsetBound_eq]
  exact WordIdealCounts.total_count_le Is ps hpositive hnorms m hm hd

/-- Both complete finite candidate-weight obligations, with all arithmetic and
actual ideal hypotheses explicit and no unproved abstract count function. -/
theorem actual_candidate_bounds (Is : List (Ideal (𝓞 K))) (hIs : Is.Nodup)
    (hcoprime : (Is.toFinset : Set (Ideal (𝓞 K))).Pairwise IsCoprime)
    (ps : List ℕ) (hprod : Is.prod = Ideal.span {(ps.prod : 𝓞 K)})
    (hpositive : ∀ p ∈ ps, 0 < p)
    (hnorms : Is.map Ideal.absNorm = Weights.repeatedNorms (Module.finrank ℚ K) ps)
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < Module.finrank ℚ K) :
    (∀ e, e < 2 ^ Is.length →
      countBelow (candidates (K := K) ps.prod m).card
        (fun r => DivisorIncidence.subsetAllowed (squareBits Is ps.prod m r) (wordAt Is e)) ≤
          subsetBound Is ps.prod m e) ∧
    sumBelow (2 ^ Is.length) (subsetBound Is ps.prod m) ≤
      (17 * m ^ 2 * (ps.map (fun p => p + 1)).prod) ^ Module.finrank ℚ K := by
  refine ⟨?_, total_subsetBound_le Is ps hpositive hnorms m hm hd⟩
  intro e he
  exact subset_count_le Is hIs hcoprime ps.prod m hprod e he

end JSP1012.CandidateWeights

#print axioms JSP1012.CandidateWeights.wordAt_mem
#print axioms JSP1012.CandidateWeights.countBelow_eq_allowed_card
#print axioms JSP1012.CandidateWeights.allowedCandidates_subset_extra
#print axioms JSP1012.CandidateWeights.subset_count_le
#print axioms JSP1012.CandidateWeights.total_subsetBound_le
#print axioms JSP1012.CandidateWeights.actual_candidate_bounds
