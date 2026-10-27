import SignedResidueVectors
import SplitResidueData
import PrimeCoordinateLists

/-!
# One fixed actual root for each actual split-prime coordinate

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.

GoodCoordinate records actual ideal/quotient properties,
not abstract ring laws. Its number-field inhabitants are CONSTRUCTED from
the verified degree-saturation and finite-field root theorems. Root choice is
made once in the coordinate list and is never allowed to depend on a point.
-/

noncomputable section

namespace JSP1012.LocalResidueCoordinates

open NumberField SignedResidueVectors

structure GoodCoordinate (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Infinite R] extends Coordinate R where
  maximal : I.IsMaximal
  norm_eq : I.absNorm = q
  root : (Ideal.Quotient.mk I r) ^ 2 = -(1 : R ⧸ I)
  two_ne : (1 : R ⧸ I) + 1 ≠ 0

/-- The quotient sign has its actual arithmetic consequence in the actual ideal. -/
theorem norm_mem_of_permission {R : Type*} [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Infinite R]
    (c : GoodCoordinate R) (sign : Bool) (x y : R)
    (h : (if sign then (c.toCoordinate.permissions x y).2
      else (c.toCoordinate.permissions x y).1) = true) :
    x ^ 2 + y ^ 2 ∈ c.I := by
  have hzero := (Coordinate.permission_eq_true_iff c.toCoordinate sign x y).mp h
  have hroot : Ideal.Quotient.mk c.I c.r * Ideal.Quotient.mk c.I c.r = -1 := by
    simpa only [pow_two] using c.root
  apply MathlibBridge.norm_mem_ideal_of_either_sign c.I x y c.r hroot
  cases sign with
  | false => exact Or.inr hzero
  | true => exact Or.inl hzero

/-- Both actual local signs give membership in the square of that SAME ideal. -/
theorem norm_mem_square_of_both_permissions {R : Type*} [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Infinite R]
    (c : GoodCoordinate R) (x y : R)
    (hminus : (c.toCoordinate.permissions x y).1 = true)
    (hplus : (c.toCoordinate.permissions x y).2 = true) :
    x ^ 2 + y ^ 2 ∈ c.I ^ 2 := by
  letI : c.I.IsMaximal := c.maximal
  have hroot : Ideal.Quotient.mk c.I c.r * Ideal.Quotient.mk c.I c.r = -1 := by
    simpa only [pow_two] using c.root
  exact MathlibBridge.norm_mem_ideal_square_of_both_signs c.I c.two_ne x y c.r hroot
    ((Coordinate.permission_eq_true_iff c.toCoordinate true x y).mp hplus)
    ((Coordinate.permission_eq_true_iff c.toCoordinate false x y).mp hminus)

section NumberFieldConstruction

variable {K : Type*} [Field K] [NumberField K]

/-- Actual finite-field root choice, made once for an actual factor ideal. -/
def coordinateOfFactor {q : ℕ} (hq : q.Prime) (hmod : q % 4 = 1)
    (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) : GoodCoordinate (𝓞 K) := by
  let hex := SplitResidueData.exists_root_representative hq hmod factors hcard hfactors P hP
  exact {
    I := P
    q := q
    finite := SplitDegreeSaturation.quotient_finite_of_degree_many_factors
      hq factors hcard hfactors P hP
    hcard := SplitDegreeSaturation.quotient_card_eq_prime_of_degree_many_factors
      hq factors hcard hfactors P hP
    r := Classical.choose hex
    maximal := (hfactors P hP).1
    norm_eq := SplitDegreeSaturation.absNorm_eq_prime_of_degree_many_factors
      hq factors hcard hfactors P hP
    root := (Classical.choose_spec hex).1
    two_ne := (Classical.choose_spec hex).2 }

/-- Every member of the actual coordinate list has actual good residue data.
The numerical radix is its DERIVED actual ideal norm. -/
theorem exists_goodCoordinate (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ PrimeCoordinateLists.coordinates ps d factors hcard) :
    ∃ c : GoodCoordinate (𝓞 K), c.I = P ∧ c.q = P.absNorm := by
  obtain ⟨j, q, heq⟩ := (PrimeCoordinateLists.mem_coordinates_iff ps d factors hcard P).mp hP
  let c := coordinateOfFactor (hprime q.val q.property) (hmod q.val q.property)
    (factors q.val) ((hcard q.val q.property).trans hd) (hfactors q.val q.property)
    (PrimeCoordinateLists.factorAt ps d factors hcard q j)
    (PrimeCoordinateLists.factorAt_mem ps d factors hcard q j)
  refine ⟨c, heq, ?_⟩
  change q.val = P.absNorm
  rw [← heq]
  exact (PrimeCoordinateLists.factorAt_absNorm ps d hd factors hcard hprime hfactors q j).symm


/-- One fixed good-coordinate choice for one actual member of the underlying
ideal list. Neither points nor signs are arguments of this choice function. -/
def goodCoordinateAt (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : {P : Ideal (𝓞 K) // P ∈ PrimeCoordinateLists.coordinates ps d factors hcard}) :
    GoodCoordinate (𝓞 K) :=
  Classical.choose (exists_goodCoordinate ps d hd factors hcard hprime hmod hfactors P.val P.property)

/-- The chosen data really lie over that same ideal and have its actual norm.
These are choose_spec conclusions, not separately assumed correspondence data. -/
theorem goodCoordinateAt_spec (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : {P : Ideal (𝓞 K) // P ∈ PrimeCoordinateLists.coordinates ps d factors hcard}) :
    (goodCoordinateAt ps d hd factors hcard hprime hmod hfactors P).I = P.val ∧
      (goodCoordinateAt ps d hd factors hcard hprime hmod hfactors P).q = P.val.absNorm :=
  Classical.choose_spec
    (exists_goodCoordinate ps d hd factors hcard hprime hmod hfactors P.val P.property)

/-- Actual root/quotient data in precisely the original coordinate-ideal order.
The chosen r in each list entry is fixed before any points are supplied. -/
def goodCoordinates (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    List (GoodCoordinate (𝓞 K)) :=
  (PrimeCoordinateLists.coordinates ps d factors hcard).attach.map
    (goodCoordinateAt ps d hd factors hcard hprime hmod hfactors)

/-- Exact ideal-list correspondence of the actual chosen data. -/
theorem goodCoordinates_ideals (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (goodCoordinates ps d hd factors hcard hprime hmod hfactors).map (fun c => c.I) =
      PrimeCoordinateLists.coordinates ps d factors hcard := by
  calc
    _ = (PrimeCoordinateLists.coordinates ps d factors hcard).attach.map Subtype.val := by
      simp only [goodCoordinates, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro P hP
      exact (goodCoordinateAt_spec ps d hd factors hcard hprime hmod hfactors P).1
    _ = _ := List.attach_map_subtype_val _

/-- Exact radix-list correspondence, again derived from the actual choice proof. -/
theorem goodCoordinates_radices_eq_norms (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (goodCoordinates ps d hd factors hcard hprime hmod hfactors).map (fun c => c.q) =
      (PrimeCoordinateLists.coordinates ps d factors hcard).map Ideal.absNorm := by
  calc
    _ = (PrimeCoordinateLists.coordinates ps d factors hcard).attach.map
        (fun P => P.val.absNorm) := by
      simp only [goodCoordinates, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro P hP
      exact (goodCoordinateAt_spec ps d hd factors hcard hprime hmod hfactors P).2
    _ = _ := List.attach_map_val

/-- The ACTUAL radices have the demanded row-major repeated-norm order. -/
theorem goodCoordinates_radices (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (goodCoordinates ps d hd factors hcard hprime hmod hfactors).map (fun c => c.q) =
      Weights.repeatedNorms d ps :=
  (goodCoordinates_radices_eq_norms ps d hd factors hcard hprime hmod hfactors).trans
    (PrimeCoordinateLists.coordinates_norm_list ps d hd factors hcard hprime hfactors)

/-- No root/quotient coordinate is lost or inserted by the actual choice. -/
theorem goodCoordinates_length (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (goodCoordinates ps d hd factors hcard hprime hmod hfactors).length = d * ps.length := by
  have h := congrArg List.length
    (goodCoordinates_ideals ps d hd factors hcard hprime hmod hfactors)
  simpa only [List.length_map, PrimeCoordinateLists.coordinates_length] using h

/-- Forgetting the good arithmetic proofs still gives the EXACT radix list
used by the proved SignedResidueVectors finite-label interface. -/
theorem goodCoordinates_bases (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    SignedResidueVectors.bases
      ((goodCoordinates ps d hd factors hcard hprime hmod hfactors).map GoodCoordinate.toCoordinate) =
        Weights.repeatedNorms d ps := by
  simpa only [SignedResidueVectors.bases, List.map_map, Function.comp_def] using
    goodCoordinates_radices ps d hd factors hcard hprime hmod hfactors

/-- Consequently the actual signed-vector bin bound is precisely Q^d. -/
theorem goodCoordinates_bases_product (ps : List ℕ) (d : ℕ) (hd : d = Module.finrank ℚ K)
    (factors : ℕ → Finset (Ideal (𝓞 K))) (hcard : ∀ q ∈ ps, (factors q).card = d)
    (hprime : ∀ q ∈ ps, q.Prime) (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hfactors : ∀ q ∈ ps, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (SignedResidueVectors.bases
      ((goodCoordinates ps d hd factors hcard hprime hmod hfactors).map GoodCoordinate.toCoordinate)).prod =
        ps.prod ^ d := by
  rw [goodCoordinates_bases ps d hd factors hcard hprime hmod hfactors,
    Weights.repeatedNorms_product]

end NumberFieldConstruction

end JSP1012.LocalResidueCoordinates

#print axioms JSP1012.LocalResidueCoordinates.norm_mem_of_permission
#print axioms JSP1012.LocalResidueCoordinates.norm_mem_square_of_both_permissions
#print axioms JSP1012.LocalResidueCoordinates.coordinateOfFactor
#print axioms JSP1012.LocalResidueCoordinates.exists_goodCoordinate

#print axioms JSP1012.LocalResidueCoordinates.goodCoordinateAt_spec
#print axioms JSP1012.LocalResidueCoordinates.goodCoordinates_ideals
#print axioms JSP1012.LocalResidueCoordinates.goodCoordinates_radices
#print axioms JSP1012.LocalResidueCoordinates.goodCoordinates_length
#print axioms JSP1012.LocalResidueCoordinates.goodCoordinates_bases_product
