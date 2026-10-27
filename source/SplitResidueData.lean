import SplitDegreeSaturation
import PrimeResidue
import IdealBridge

/-!
# Actual number-field local signs from degree-many split factors

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
Its dependencies have parent-reported successful controlled builds, but this
new composition still requires its own authorized build and axiom audit.

The finite list is exactly the data returned by the Sawin tower endpoint:
`[K:ℚ]` distinct maximal ideals containing the rational prime `q ≡ 1 mod 4`.
Degree-sum saturation proves the actual residue cardinality. Finite-field
arithmetic then supplies an actual residue root of minus one, and surjectivity
of the actual quotient map LIFTS it to an integral representative. For that
SAME representative, the proved quotient/ideal adapters give both local norm
implications. No residue root, lift, norm preservation, or ideal-square
membership is postulated. No NYLL module is imported or executed.
-/

noncomputable section

namespace JSP1012.SplitResidueData

open NumberField

/-- The actual residue root has an integral representative because the actual
quotient map is surjective. Its root relation and odd characteristic are
DERIVED from the prime-cardinality residue quotient. -/
theorem exists_root_representative {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (hmod : q % 4 = 1)
    (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) :
    ∃ r : 𝓞 K, (Ideal.Quotient.mk P r) ^ 2 = -(1 : (𝓞 K) ⧸ P) ∧
      (1 : (𝓞 K) ⧸ P) + 1 ≠ 0 := by
  letI : P.IsMaximal := (hfactors P hP).1
  letI : Finite ((𝓞 K) ⧸ P) :=
    SplitDegreeSaturation.quotient_finite_of_degree_many_factors hq factors hcard hfactors P hP
  have hquotient := SplitDegreeSaturation.quotient_card_eq_prime_of_degree_many_factors
    hq factors hcard hfactors P hP
  obtain ⟨rbar, hroot, htwo⟩ :=
    PrimeResidue.quotient_exists_root_of_natCard P hq hquotient hmod
  obtain ⟨r, hlift⟩ := Ideal.Quotient.mk_surjective rbar
  refine ⟨r, ?_, htwo⟩
  rw [hlift, pow_two]
  exact hroot

/-- The complete local-sign input for one selected actual prime ideal. All
invariants and BOTH sign consequences refer to the same ideal and the same
lifted integral root `r`. In particular, the either-sign and both-sign clauses
are not separately witnessed by potentially different choices of roots. -/
theorem split_prime_local_data {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (hmod : q % 4 = 1)
    (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) :
    P.absNorm = q ∧ Nat.card ((𝓞 K) ⧸ P) = q ∧ Finite ((𝓞 K) ⧸ P) ∧
      ∃ r : 𝓞 K,
        (Ideal.Quotient.mk P r) ^ 2 = -(1 : (𝓞 K) ⧸ P) ∧
        (1 : (𝓞 K) ⧸ P) + 1 ≠ 0 ∧
        (∀ x y : 𝓞 K,
          (Ideal.Quotient.mk P x + Ideal.Quotient.mk P r * Ideal.Quotient.mk P y = 0 ∨
            Ideal.Quotient.mk P x + -(Ideal.Quotient.mk P r * Ideal.Quotient.mk P y) = 0) →
          x ^ 2 + y ^ 2 ∈ P) ∧
        (∀ x y : 𝓞 K,
          Ideal.Quotient.mk P x + Ideal.Quotient.mk P r * Ideal.Quotient.mk P y = 0 →
          Ideal.Quotient.mk P x + -(Ideal.Quotient.mk P r * Ideal.Quotient.mk P y) = 0 →
          x ^ 2 + y ^ 2 ∈ P ^ 2) := by
  letI : P.IsMaximal := (hfactors P hP).1
  have hnorm := SplitDegreeSaturation.absNorm_eq_prime_of_degree_many_factors
    hq factors hcard hfactors P hP
  have hquotient := SplitDegreeSaturation.quotient_card_eq_prime_of_degree_many_factors
    hq factors hcard hfactors P hP
  have hfinite := SplitDegreeSaturation.quotient_finite_of_degree_many_factors
    hq factors hcard hfactors P hP
  obtain ⟨r, hroot, htwo⟩ := exists_root_representative hq hmod factors hcard hfactors P hP
  have hroot_mul : Ideal.Quotient.mk P r * Ideal.Quotient.mk P r = -(1 : (𝓞 K) ⧸ P) := by
    simpa only [pow_two] using hroot
  refine ⟨hnorm, hquotient, hfinite, r, hroot, htwo, ?_, ?_⟩
  · intro x y hsign
    exact MathlibBridge.norm_mem_ideal_of_either_sign P x y r hroot_mul hsign
  · intro x y hplus hminus
    exact MathlibBridge.norm_mem_ideal_square_of_both_signs P htwo x y r hroot_mul hplus hminus

end JSP1012.SplitResidueData

#print axioms JSP1012.SplitResidueData.exists_root_representative
#print axioms JSP1012.SplitResidueData.split_prime_local_data
