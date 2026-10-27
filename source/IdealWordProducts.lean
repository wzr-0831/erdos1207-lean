import SignOverlap
import SubsetWeights
import ScaledWeights
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Actual ideal-word products and exact occurrence-weight lists

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
Its direct local dependencies are SignOverlap, SubsetWeights and ScaledWeights;
SubsetWeights additionally imports FinitePairCount. These Std modules must be
made available to the coordinated stable-Mathlib build lane before compiling.

Every Boolean word selects occurrences from an actual ideal list. Applying the
actual ideal absolute norm to every selected product yields EXACTLY the Std
occurrence-subset product list, in the same recursive order and with every
multiplicity retained. Neither norms nor ideal products are deduplicated; no
injectivity, pairwise coprimality, norm preservation, or divisor-factorization
hypothesis is used for this list identity.

The scaled aggregate theorems keep the remaining concrete correspondence
`Is.map absNorm = repeatedNorms d ps` EXPLICIT. No number-field construction or
such correspondence is asserted to exist in this module.
-/

noncomputable section

namespace JSP1012.IdealWordProducts

/-- Multiply exactly the selected coordinate occurrences, preserving list order.
A false sign contributes the identity. For shorter words, omitted coordinates
are unselected; the actual enumeration below always supplies the full length. -/
def wordProduct {M : Type*} [Monoid M] : List M → List Bool → M
  | [], _ => 1
  | _ :: _, [] => 1
  | _ :: Is, false :: word => wordProduct Is word
  | I :: Is, true :: word => I * wordProduct Is word

/-- The actual product list associated with the complete Boolean-word list. -/
def wordProducts {M : Type*} [Monoid M] (Is : List M) : List M :=
  (SignOverlap.signWords Is.length).map (wordProduct Is)

/-- Every coordinate word is retained, even if some products coincide. -/
theorem wordProducts_length {M : Type*} [Monoid M] (Is : List M) :
    (wordProducts Is).length = 2 ^ Is.length := by
  simp only [wordProducts, List.length_map, SignOverlap.signWords_length]

/-- On natural coordinate values, the explicit word traversal is precisely the
verified recursive occurrence-subset enumeration, as an exact LIST equality. -/
theorem nat_wordProduct_enumeration (ns : List ℕ) :
    (SignOverlap.signWords ns.length).map (wordProduct ns) = Weights.subsetProducts ns := by
  induction ns with
  | nil => rfl
  | cons a ns ih =>
    have hmul : (SignOverlap.signWords ns.length).map (fun word => a * wordProduct ns word) =
        ((SignOverlap.signWords ns.length).map (wordProduct ns)).map (fun n => a * n) := by
      simp only [List.map_map, Function.comp_def]
    simp only [List.length_cons, SignOverlap.signWords, List.map_append, List.map_map,
      Function.comp_def, wordProduct, Weights.subsetProducts]
    rw [hmul]
    simp only [ih]

section ActualIdealNorm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Infinite R]

/-- Actual ideal norm laws transport each actual word product, including the
empty product. The preservation equation is proved, not an extra hypothesis. -/
theorem absNorm_wordProduct (Is : List (Ideal R)) (word : List Bool) :
    (wordProduct Is word).absNorm = wordProduct (Is.map Ideal.absNorm) word := by
  induction Is generalizing word with
  | nil => simp only [wordProduct, List.map_nil, map_one]
  | cons I Is ih =>
    cases word with
    | nil => simp only [wordProduct, List.map_cons, map_one]
    | cons b word =>
      cases b with
      | false => simpa only [wordProduct, List.map_cons] using ih word
      | true => simp only [wordProduct, List.map_cons, map_mul, ih]

/-- Exact norm-list correspondence for the actual selected ideal products.
Equal numerical norms and equal resulting ideal products keep multiplicity. -/
theorem absNorm_wordProduct_enumeration (Is : List (Ideal R)) :
    (SignOverlap.signWords Is.length).map (fun word => (wordProduct Is word).absNorm) =
      Weights.subsetProducts (Is.map Ideal.absNorm) := by
  calc
    _ = (SignOverlap.signWords Is.length).map (wordProduct (Is.map Ideal.absNorm)) := by
      apply List.map_congr_left
      intro word hword
      exact absNorm_wordProduct Is word
    _ = Weights.subsetProducts (Is.map Ideal.absNorm) := by
      simpa only [List.length_map] using nat_wordProduct_enumeration (Is.map Ideal.absNorm)

/-- Named actual-entries form consumed directly by the scaled-count theorem. -/
theorem wordProducts_norm_list (Is : List (Ideal R)) :
    (wordProducts Is).map Ideal.absNorm = Weights.subsetProducts (Is.map Ideal.absNorm) := by
  simpa only [wordProducts, List.map_map, Function.comp_def] using absNorm_wordProduct_enumeration Is

/-- Exact scaled sum over ACTUAL ideal-word products, after the remaining
coordinate norm-list identification is separately proved. -/
theorem scaled_wordProducts_sum (Is : List (Ideal R)) (d c : ℕ) (ps : List ℕ)
    (hpositive : ∀ p, p ∈ ps → 0 < p)
    (hnorms : Is.map Ideal.absNorm = Weights.repeatedNorms d ps) :
    ((wordProducts Is).map (fun I => (c * ps.prod) ^ d / I.absNorm)).sum =
      (c * (ps.map (fun p => p + 1)).prod) ^ d := by
  have hmap : (wordProducts Is).map (fun I => (c * ps.prod) ^ d / I.absNorm) =
      ((wordProducts Is).map Ideal.absNorm).map (fun a => (c * ps.prod) ^ d / a) := by
    simp only [List.map_map, Function.comp_def]
  rw [hmap, wordProducts_norm_list, hnorms,
    ScaledWeights.scaled_reciprocal_subset_sum d c ps hpositive]

/-- Candidate counts over actual ideal products aggregate with the exact
occurrence multiplicities. Counts are not identified merely by numerical norm. -/
theorem aggregate_wordProduct_counts_le (Is : List (Ideal R)) (count : Ideal R → ℕ)
    (d c : ℕ) (ps : List ℕ) (hpositive : ∀ p, p ∈ ps → 0 < p)
    (hnorms : Is.map Ideal.absNorm = Weights.repeatedNorms d ps)
    (hcount : ∀ I, I ∈ wordProducts Is → count I ≤ (c * ps.prod) ^ d / I.absNorm) :
    ((wordProducts Is).map count).sum ≤ (c * (ps.map (fun p => p + 1)).prod) ^ d := by
  have sum_le (xs : List (Ideal R)) :
      (∀ I, I ∈ xs → count I ≤ (c * ps.prod) ^ d / I.absNorm) →
      (xs.map count).sum ≤ (xs.map (fun I => (c * ps.prod) ^ d / I.absNorm)).sum := by
    induction xs with
    | nil => intro _; exact Nat.le_refl 0
    | cons I xs ih =>
      intro hxs
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hxs I (by simp))
        (ih (fun J hJ => hxs J (by simp only [List.mem_cons]; exact Or.inr hJ)))
  calc
    _ ≤ ((wordProducts Is).map (fun I => (c * ps.prod) ^ d / I.absNorm)).sum :=
      sum_le (wordProducts Is) hcount
    _ = _ := scaled_wordProducts_sum Is d c ps hpositive hnorms

end ActualIdealNorm

/-- Repeated coordinate values MUST retain their repeated middle products. -/
example : wordProducts ([5, 5] : List ℕ) = [1, 5, 5, 25] := by decide

example : wordProducts ([] : List ℕ) = [1] := by decide

end JSP1012.IdealWordProducts

#print axioms JSP1012.IdealWordProducts.nat_wordProduct_enumeration
#print axioms JSP1012.IdealWordProducts.absNorm_wordProduct
#print axioms JSP1012.IdealWordProducts.wordProducts_norm_list
#print axioms JSP1012.IdealWordProducts.scaled_wordProducts_sum
#print axioms JSP1012.IdealWordProducts.aggregate_wordProduct_counts_le
