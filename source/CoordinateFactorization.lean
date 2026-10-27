import PrimeCoordinateLists
import SplitIdealProduct
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Actual full coordinate ideal product

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
A coordinated successful build and axiom audit are required before claiming
any new verified milestone.

The coordinate ideals are the actual row-major list from PrimeCoordinateLists.
Their derived Nodup permits taking its actual finset without losing factors.
Every coordinate is a maximal factor over one prime of `ps`; that prime divides
`ps.prod`, so the rational product belongs to every coordinate ideal.
Pairwise coprimality gives principal-ideal containment in the coordinate product.

The derived exact norm list gives norm `(ps.prod)^d`; the actual principal ideal
has the SAME positive norm. The already proved COMPARABLE-ideal norm argument
then gives equality. No arrangement, permutation, exhaustion, arbitrary norm
injectivity, or global ideal factorization is assumed. The empty prime list,
whose product is one and whose coordinate product is the unit ideal, is allowed.
No NYLL module is imported or executed.
-/

noncomputable section

namespace JSP1012.CoordinateFactorization

open NumberField
open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- Actual finset of the actual coordinates; Nodup is established separately. -/
def coordinateSet (ps : List ℕ) (d : ℕ) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d) : Finset (Ideal (𝓞 K)) := by
  classical
  exact (PrimeCoordinateLists.coordinates ps d factors hcard).toFinset

@[simp] theorem mem_coordinateSet (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (P : Ideal (𝓞 K)) :
    P ∈ coordinateSet ps d factors hcard ↔
      P ∈ PrimeCoordinateLists.coordinates ps d factors hcard := by
  classical
  exact List.mem_toFinset

/-- An actual coordinate has an actual prime/factor witness. -/
theorem coordinate_factor_witness (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (P : Ideal (𝓞 K)) (hP : P ∈ PrimeCoordinateLists.coordinates ps d factors hcard) :
    ∃ q, q ∈ ps ∧ P ∈ factors q := by
  obtain ⟨j, q, hcoord⟩ :=
    (PrimeCoordinateLists.mem_coordinates_iff ps d factors hcard P).mp hP
  refine ⟨q.val, q.property, ?_⟩
  rw [← hcoord]
  exact PrimeCoordinateLists.factorAt_mem ps d factors hcard q j

theorem coordinate_isMaximal (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ PrimeCoordinateLists.coordinates ps d factors hcard) :
    P.IsMaximal := by
  obtain ⟨q, hq, hfactor⟩ := coordinate_factor_witness ps d factors hcard P hP
  exact (hfactors q hq P hfactor).1

/-- The actual rational product belongs to every actual coordinate ideal. -/
theorem coordinate_contains_product (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ PrimeCoordinateLists.coordinates ps d factors hcard) :
    (ps.prod : 𝓞 K) ∈ P := by
  obtain ⟨q, hq, hfactor⟩ := coordinate_factor_witness ps d factors hcard P hP
  have hqmem : (q : 𝓞 K) ∈ P := (hfactors q hq P hfactor).2
  obtain ⟨a, ha⟩ := List.dvd_prod hq
  rw [ha, Nat.cast_mul]
  exact P.mul_mem_right (a : 𝓞 K) hqmem

/-- Distinct coordinate ideals are genuinely coprime by their derived maximality. -/
theorem pairwise_coprime (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (coordinateSet ps d factors hcard : Set (Ideal (𝓞 K))).Pairwise IsCoprime := by
  intro P hP Q hQ hPQ
  have hPM := coordinate_isMaximal ps d factors hcard hfactors P
    ((mem_coordinateSet ps d factors hcard P).mp hP)
  have hQM := coordinate_isMaximal ps d factors hcard hfactors Q
    ((mem_coordinateSet ps d factors hcard Q).mp hQ)
  exact Ideal.isCoprime_iff_sup_eq.mpr (hPM.coprime_of_ne hQM hPQ)

/-- Actual intersection/product equality supplies the needed containment. -/
theorem span_product_le_coordinate_product (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    Ideal.span {(ps.prod : 𝓞 K)} ≤ ∏ P ∈ coordinateSet ps d factors hcard, P := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (pairwise_coprime ps d factors hcard hfactors)]
  apply le_iInf
  intro P
  apply le_iInf
  intro hP
  apply (Ideal.span_singleton_le_iff_mem P).mpr
  exact coordinate_contains_product ps d factors hcard hfactors P
    ((mem_coordinateSet ps d factors hcard P).mp hP)

/-- Exact norm of the actual full product. Taking a finset is justified by
DERIVED Nodup of the ideal list, not by deduplicating its numerical norm list. -/
theorem absNorm_product (ps : List ℕ) (hps : ps.Nodup) (d : ℕ)
    (hd : d = Module.finrank ℚ K) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d) (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (∏ P ∈ coordinateSet ps d factors hcard, P).absNorm = ps.prod ^ d := by
  classical
  have hnodup := PrimeCoordinateLists.coordinates_nodup ps hps d factors hcard hprime hfactors
  have hnorms := PrimeCoordinateLists.coordinates_norm_list ps d hd factors hcard hprime hfactors
  calc
    (∏ P ∈ coordinateSet ps d factors hcard, P).absNorm =
        ∏ P ∈ coordinateSet ps d factors hcard, P.absNorm := by rw [map_prod]
    _ = ((PrimeCoordinateLists.coordinates ps d factors hcard).map Ideal.absNorm).prod := by
      exact List.prod_toFinset Ideal.absNorm hnodup
    _ = (Weights.repeatedNorms d ps).prod := by rw [hnorms]
    _ = ps.prod ^ d := Weights.repeatedNorms_product d ps

/-- The requested ACTUAL full coordinate ideal factorization. -/
theorem product_eq_span (ps : List ℕ) (hps : ps.Nodup) (d : ℕ)
    (hd : d = Module.finrank ℚ K) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d) (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (∏ P ∈ coordinateSet ps d factors hcard, P) = Ideal.span {(ps.prod : 𝓞 K)} := by
  have hQ : 0 < ps.prod := List.prod_pos (fun q hq => (hprime q hq).pos)
  have hprincipal : (Ideal.span {(ps.prod : 𝓞 K)}).absNorm = ps.prod ^ d := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, ← hd]
  have hproduct := absNorm_product ps hps d hd factors hcard hprime hfactors
  have hpositive : 0 < (Ideal.span {(ps.prod : 𝓞 K)}).absNorm := by
    rw [hprincipal]
    exact pow_pos hQ _
  exact (SplitIdealProduct.eq_of_le_of_positive_absNorm_eq
    (Ideal.span {(ps.prod : 𝓞 K)}) (∏ P ∈ coordinateSet ps d factors hcard, P)
    (span_product_le_coordinate_product ps d factors hcard hfactors) hpositive
    (hprincipal.trans hproduct.symm)).symm

/-- List-product form consumed by the occurrence-word ideal construction. -/
theorem list_product_eq_span (ps : List ℕ) (hps : ps.Nodup) (d : ℕ)
    (hd : d = Module.finrank ℚ K) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d) (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (PrimeCoordinateLists.coordinates ps d factors hcard).prod =
      Ideal.span {(ps.prod : 𝓞 K)} := by
  classical
  have hnodup := PrimeCoordinateLists.coordinates_nodup ps hps d factors hcard hprime hfactors
  have heq : (∏ P ∈ coordinateSet ps d factors hcard, P) =
      (PrimeCoordinateLists.coordinates ps d factors hcard).prod := by
    simpa only [coordinateSet, List.map_id, id_eq] using List.prod_toFinset id hnodup
  exact heq.symm.trans (product_eq_span ps hps d hd factors hcard hprime hfactors)

end JSP1012.CoordinateFactorization

#print axioms JSP1012.CoordinateFactorization.coordinate_isMaximal
#print axioms JSP1012.CoordinateFactorization.pairwise_coprime
#print axioms JSP1012.CoordinateFactorization.absNorm_product
#print axioms JSP1012.CoordinateFactorization.product_eq_span
#print axioms JSP1012.CoordinateFactorization.list_product_eq_span
