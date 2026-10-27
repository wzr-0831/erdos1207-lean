import SplitDegreeSaturation
import SplitIdealProduct
import SubsetWeights
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup

/-!
# Actual split-prime coordinate lists in the required row order

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
A coordinated successful build and axiom audit are required before reporting
these declarations as verified results.

For every prime occurrence in `ps`, the ACTUAL factor finset is enumerated by
its actual equivalence with `Fin d`. Row `j` takes the `j`-th factor for each
prime, IN THE ORIGINAL ORDER OF `ps`; rows are concatenated for `j=0,...,d-1`.
Consequently the exact norm list is `ps ++ ps ++ ... ++ ps` (d rows), not a
prime-by-prime list with d equal consecutive values. This closes an ordering
obligation, not merely a multiset/permutation obligation.

With `ps.Nodup`, within-prime enumeration injectivity and actual contraction
for different rational primes prove that the entire ideal list is Nodup.
Equal NUMERICAL norms across different rows are retained and never merged.
No enumeration, norm order, or ideal-coordinate injectivity is postulated.
No NYLL module is imported or executed.
-/

noncomputable section

namespace JSP1012.PrimeCoordinateLists

open NumberField

private theorem flatMap_const_repeated {α : Type*} (rows : List α) (ps : List ℕ) :
    rows.flatMap (fun _ => ps) = Weights.repeatedNorms rows.length ps := by
  induction rows with
  | nil => rfl
  | cons j rows ih =>
    simp only [List.flatMap_cons, List.length_cons, Weights.repeatedNorms, ih]

section Coordinates

variable {K : Type*} [Field K] [NumberField K]

/-- The actual j-th factor of one selected prime, through a proved cardinal
bijection. The equivalence is NOT an assumed enumeration function. -/
def factorAt (ps : List ℕ) (d : ℕ) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d)
    (q : {q : ℕ // q ∈ ps}) (j : Fin d) : Ideal (𝓞 K) :=
  ((Finset.equivFinOfCardEq (hcard q.val q.property)).symm j).val

theorem factorAt_mem (ps : List ℕ) (d : ℕ) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d)
    (q : {q : ℕ // q ∈ ps}) (j : Fin d) : factorAt ps d factors hcard q j ∈ factors q.val :=
  ((Finset.equivFinOfCardEq (hcard q.val q.property)).symm j).property

theorem factorAt_injective (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (q : {q : ℕ // q ∈ ps}) : Function.Injective (factorAt ps d factors hcard q) := by
  intro i j hij
  apply (Finset.equivFinOfCardEq (hcard q.val q.property)).symm.injective
  exact Subtype.ext hij

/-- One row traverses the original prime list, not a sorted/deduplicated list. -/
def row (ps : List ℕ) (d : ℕ) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d) (j : Fin d) : List (Ideal (𝓞 K)) :=
  ps.attach.map (fun q => factorAt ps d factors hcard q j)

/-- Row-major actual coordinates: prime order inside each row, rows j=0,...,d-1. -/
def coordinates (ps : List ℕ) (d : ℕ) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hcard : ∀ q ∈ ps, (factors q).card = d) : List (Ideal (𝓞 K)) :=
  (List.finRange d).flatMap (row ps d factors hcard)

/-- Exact alternate description by ordered (row,prime) occurrence coordinates. -/
theorem coordinates_eq_product_map (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d) :
    coordinates ps d factors hcard =
      (List.product (List.finRange d) ps.attach).map
        (fun z => factorAt ps d factors hcard z.2 z.1) := by
  simp only [coordinates, row, List.product, List.map_flatMap, List.map_map, Function.comp_def]
  rfl

/-- Structural length, without any arithmetic assumptions on prime norms. -/
theorem coordinates_length (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d) :
    (coordinates ps d factors hcard).length = d * ps.length := by
  rw [coordinates_eq_product_map, List.length_map]
  change ((List.finRange d) ×ˢ ps.attach).length = d * ps.length
  rw [List.length_product, List.length_finRange, List.length_attach]

theorem mem_coordinates_iff (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (P : Ideal (𝓞 K)) :
    P ∈ coordinates ps d factors hcard ↔
      ∃ j : Fin d, ∃ q : {q : ℕ // q ∈ ps}, factorAt ps d factors hcard q j = P := by
  simp only [coordinates, row, List.mem_flatMap, List.mem_map, List.mem_finRange,
    List.mem_attach, true_and]

/-- Each actual coordinate has its actual prime norm, by degree saturation. -/
theorem factorAt_absNorm (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (q : {q : ℕ // q ∈ ps}) (j : Fin d) :
    (factorAt ps d factors hcard q j).absNorm = q.val := by
  exact SplitDegreeSaturation.absNorm_eq_prime_of_degree_many_factors
    (hprime q.val q.property) (factors q.val) ((hcard q.val q.property).trans hd)
    (hfactors q.val q.property) (factorAt ps d factors hcard q j)
    (factorAt_mem ps d factors hcard q j)

/-- The exact norm list of EVERY row is the original list `ps`. -/
theorem row_norm_list (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (j : Fin d) : (row ps d factors hcard j).map Ideal.absNorm = ps := by
  calc
    (row ps d factors hcard j).map Ideal.absNorm = ps.attach.map Subtype.val := by
      simp only [row, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro q hq
      exact factorAt_absNorm ps d hd factors hcard hprime hfactors q j
    _ = ps := List.attach_map_subtype_val ps

/-- The demanded exact ordering: d copies of the WHOLE prime list. This is a
list equality, not an equality after sorting or taking a finset. -/
theorem coordinates_norm_list (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (coordinates ps d factors hcard).map Ideal.absNorm = Weights.repeatedNorms d ps := by
  calc
    _ = (List.finRange d).flatMap (fun j => (row ps d factors hcard j).map Ideal.absNorm) := by
      rw [coordinates, List.map_flatMap]
    _ = (List.finRange d).flatMap (fun _ => ps) :=
      congrArg (fun f : Fin d → List ℕ => (List.finRange d).flatMap f)
        (funext (fun j => row_norm_list ps d hd factors hcard hprime hfactors j))
    _ = Weights.repeatedNorms d ps := by
      simpa only [List.length_finRange] using flatMap_const_repeated (List.finRange d) ps

/-- Distinct (row,prime) coordinates give distinct ACTUAL ideals. Across prime
values this uses contraction, not numerical norm injectivity. Within one prime
it uses the actual factor-finset equivalence. -/
theorem factorAt_pair_injective (ps : List ℕ) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    Function.Injective (fun z : Fin d × {q : ℕ // q ∈ ps} =>
      factorAt ps d factors hcard z.2 z.1) := by
  intro a b hab
  have hq : a.2 = b.2 := by
    apply Subtype.ext
    by_contra hne
    exact SplitIdealProduct.ideals_over_distinct_primes_ne
      (hprime a.2.val a.2.property) (hprime b.2.val b.2.property) hne
      (factorAt ps d factors hcard a.2 a.1) (factorAt ps d factors hcard b.2 b.1)
      (hfactors a.2.val a.2.property _ (factorAt_mem ps d factors hcard a.2 a.1)).1
      (hfactors b.2.val b.2.property _ (factorAt_mem ps d factors hcard b.2 b.1)).1
      (hfactors a.2.val a.2.property _ (factorAt_mem ps d factors hcard a.2 a.1)).2
      (hfactors b.2.val b.2.property _ (factorAt_mem ps d factors hcard b.2 b.1)).2 hab
  have hsame : factorAt ps d factors hcard a.2 a.1 =
      factorAt ps d factors hcard a.2 b.1 := by simpa only [← hq] using hab
  have hj : a.1 = b.1 := factorAt_injective ps d factors hcard a.2 hsame
  exact Prod.ext hj hq

/-- Nodup of the ACTUAL coordinate list is derived, never assumed. Repeated
rational-prime norms across rows do not violate distinctness of the ideals. -/
theorem coordinates_nodup (ps : List ℕ) (hps : ps.Nodup) (d : ℕ)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (coordinates ps d factors hcard).Nodup := by
  rw [coordinates_eq_product_map]
  exact ((List.nodup_finRange d).product hps.attach).map
    (factorAt_pair_injective ps d factors hcard hprime hfactors)

end Coordinates
end JSP1012.PrimeCoordinateLists

#print axioms JSP1012.PrimeCoordinateLists.coordinates_length
#print axioms JSP1012.PrimeCoordinateLists.factorAt_absNorm
#print axioms JSP1012.PrimeCoordinateLists.coordinates_norm_list
#print axioms JSP1012.PrimeCoordinateLists.factorAt_pair_injective
#print axioms JSP1012.PrimeCoordinateLists.coordinates_nodup
