/-
Released under the Apache 2.0 license.

Mathlib-only extraction of the new exact-degree helper from ExactDegreeTower.lean.
The theorem statement and proof body are preserved byte-for-byte; the frozen
ExactDegreeTower.lean is not modified by this extraction.

SOURCE ONLY at creation: no compilation or kernel verification by this author.
Target: Lean 4.35.0-rc2; Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
No NYLL module is imported. This file is for a separately coordinated early
rc2 API check, not a claim that the arithmetic tower input has been verified.
-/

import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.GroupTheory.Nilpotent

namespace ClassFieldTower.Sawin

/-- A finite Galois 2-extension of sufficiently large degree contains an
actual ambient finite Galois subfield of degree exactly `2^i`. -/
theorem exists_finiteGalois_subfield_finrank_eq_pow_two
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hP : IsPGroup 2 (E ≃ₐ[ℚ] E)) (i : ℕ)
    (hi : 2 ^ i ≤ Module.finrank ℚ E) :
    ∃ F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ),
      F.toIntermediateField ≤ E.toIntermediateField ∧
        Module.finrank ℚ F = 2 ^ i := by
  classical
  let instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let instGalE : IsGalois ℚ E.toIntermediateField := E.isGalois
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have hia : i ≤ a := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ i ≤ Module.finrank ℚ E := hi
      _ = Nat.card (E ≃ₐ[ℚ] E) := (IsGalois.card_aut_eq_finrank ℚ E).symm
      _ = 2 ^ a := ha
  have hdvd : 2 ^ i ∣ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [ha]
    exact Nat.pow_dvd_pow 2 hia
  let instNilpotent : Group.IsNilpotent (E ≃ₐ[ℚ] E) := hP.isNilpotent
  obtain ⟨H, hHindex, hHnormal⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  let instNormalH : H.Normal := hHnormal
  let K : IntermediateField ℚ E.toIntermediateField := IntermediateField.fixedField H
  let instGalK : IsGalois ℚ K := IsGalois.of_fixedField_normal_subgroup H
  have hKdegree : Module.finrank ℚ K = 2 ^ i := by
    change Module.finrank ℚ (IntermediateField.fixedField H) = 2 ^ i
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField, hHindex]
  let e : K ≃ₐ[ℚ] IntermediateField.lift K := IntermediateField.liftAlgEquiv K
  let F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := IntermediateField.lift K
      finiteDimensional := e.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv e }
  refine ⟨F, IntermediateField.lift_le K, ?_⟩
  change Module.finrank ℚ (IntermediateField.lift K) = 2 ^ i
  rw [← e.toLinearEquiv.finrank_eq]
  exact hKdegree

end ClassFieldTower.Sawin
