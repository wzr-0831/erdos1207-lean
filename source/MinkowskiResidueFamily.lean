import LocalResidueCoordinates
import CoordinateFactorization
import LocalSignArithmetic
import WordIdealCounts
import Mathlib.Data.List.GetD

/-!
# Actual split-prime data packaged for the finite Minkowski-grid sieve

Source preparation. The hypotheses are exactly finite pieces of the split
field input: distinct rational primes 1 mod4 and degree-many distinct maximal
ideals containing each prime. Residue roots, quotient cardinalities, norm
lists, coprimality and principal-ideal product are DERIVED, not record fields.
All roots are chosen once in the data list, before any point arguments.
-/

noncomputable section

namespace JSP1012.MinkowskiResidueFamily

open NumberField LocalResidueCoordinates SignedResidueVectors
open scoped BigOperators

structure SplitFamily (K : Type*) [Field K] [NumberField K] where
  ps : List ℕ
  nodup : ps.Nodup
  prime : ∀ q ∈ ps, q.Prime
  mod4 : ∀ q ∈ ps, q % 4 = 1
  factors : ℕ → Finset (Ideal (𝓞 K))
  card : ∀ q ∈ ps, (factors q).card = Module.finrank ℚ K
  maximal : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P

variable {K : Type*} [Field K] [NumberField K]

def coordinateData (f : SplitFamily K) : List (GoodCoordinate (𝓞 K)) :=
  goodCoordinates f.ps (Module.finrank ℚ K) rfl f.factors f.card f.prime f.mod4 f.maximal

def idealList (f : SplitFamily K) : List (Ideal (𝓞 K)) :=
  (coordinateData f).map (fun c => c.I)

def quotientCoordinates (f : SplitFamily K) : List (Coordinate (𝓞 K)) :=
  (coordinateData f).map GoodCoordinate.toCoordinate

def Q (f : SplitFamily K) : ℕ := f.ps.prod
def k (f : SplitFamily K) : ℕ := (coordinateData f).length
def radixList (f : SplitFamily K) : List ℕ := bases (quotientCoordinates f)

theorem Q_pos (f : SplitFamily K) : 0 < Q f :=
  List.prod_pos (fun q hq => (f.prime q hq).pos)

theorem idealList_eq (f : SplitFamily K) :
    idealList f = PrimeCoordinateLists.coordinates f.ps (Module.finrank ℚ K) f.factors f.card :=
  goodCoordinates_ideals f.ps _ rfl f.factors f.card f.prime f.mod4 f.maximal

theorem idealList_nodup (f : SplitFamily K) : (idealList f).Nodup := by
  rw [idealList_eq]
  exact PrimeCoordinateLists.coordinates_nodup f.ps f.nodup _ f.factors f.card f.prime f.maximal

theorem idealList_norms (f : SplitFamily K) :
    (idealList f).map Ideal.absNorm = Weights.repeatedNorms (Module.finrank ℚ K) f.ps := by
  rw [idealList_eq]
  exact PrimeCoordinateLists.coordinates_norm_list f.ps _ rfl f.factors f.card f.prime f.maximal

theorem idealList_length (f : SplitFamily K) : (idealList f).length = k f := by
  simp only [idealList, List.length_map, k]

theorem k_eq (f : SplitFamily K) : k f = Module.finrank ℚ K * f.ps.length :=
  goodCoordinates_length f.ps _ rfl f.factors f.card f.prime f.mod4 f.maximal

theorem radixList_eq (f : SplitFamily K) :
    radixList f = Weights.repeatedNorms (Module.finrank ℚ K) f.ps :=
  goodCoordinates_bases f.ps _ rfl f.factors f.card f.prime f.mod4 f.maximal

theorem radixList_product (f : SplitFamily K) : (radixList f).prod = Q f ^ Module.finrank ℚ K :=
  goodCoordinates_bases_product f.ps _ rfl f.factors f.card f.prime f.mod4 f.maximal

theorem idealList_product (f : SplitFamily K) :
    (idealList f).prod = Ideal.span {(Q f : 𝓞 K)} := by
  rw [idealList_eq]
  exact CoordinateFactorization.list_product_eq_span f.ps f.nodup _ rfl
    f.factors f.card f.prime f.maximal

def idealSet (f : SplitFamily K) : Finset (Ideal (𝓞 K)) := by
  classical
  exact (idealList f).toFinset

theorem pairwise_coprime (f : SplitFamily K) :
    (idealSet f : Set (Ideal (𝓞 K))).Pairwise IsCoprime := by
  classical
  have hset : idealSet f = CoordinateFactorization.coordinateSet f.ps
      (Module.finrank ℚ K) f.factors f.card := by
    simp only [idealSet, idealList_eq, CoordinateFactorization.coordinateSet]
  rw [hset]
  exact CoordinateFactorization.pairwise_coprime f.ps _ f.factors f.card f.maximal

/-- A sign word is only used under its VALID finite-family index. -/
def word (f : SplitFamily K) (e : ℕ) : List Bool :=
  (SignOverlap.signWords (k f)).getD e []

theorem word_mem (f : SplitFamily K) {e : ℕ} (he : e < 2 ^ k f) :
    word f e ∈ SignOverlap.signWords (k f) := by
  have he' : e < (SignOverlap.signWords (k f)).length := by
    simpa only [SignOverlap.signWords_length] using he
  unfold word
  rw [List.getD_eq_getElem _ _ he']
  exact List.getElem_mem he'

theorem word_length (f : SplitFamily K) {e : ℕ} (he : e < 2 ^ k f) :
    (word f e).length = k f :=
  (SignOverlap.mem_signWords_iff (k f) (word f e)).mp (word_mem f he)

/-- Every actual point has a bounded signed residue vector, using the same
preselected root in each actual coordinate. No CRT cardinality is assumed. -/
theorem digits_bounded (f : SplitFamily K) {e : ℕ} (he : e < 2 ^ k f)
    (x y : 𝓞 K) :
    Radix.Bounded (radixList f) (digits (quotientCoordinates f) (word f e) x y) := by
  apply SignedResidueVectors.digits_bounded
  simpa only [quotientCoordinates, List.length_map, k] using word_length f he

end JSP1012.MinkowskiResidueFamily

#print axioms JSP1012.MinkowskiResidueFamily.idealList_product
#print axioms JSP1012.MinkowskiResidueFamily.radixList_product
#print axioms JSP1012.MinkowskiResidueFamily.pairwise_coprime
#print axioms JSP1012.MinkowskiResidueFamily.digits_bounded
