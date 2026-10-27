/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.

The arithmetic packaging below is adapted from the audited NYLL file
Nyll/SawinTotallyRealTowers/SawinTotallyRealTower.lean, whose original
statement preserves Copyright 2025 The Formal Conjectures Authors.
The exact-degree fixed-field extraction and strengthened wrappers are new.

SOURCE ONLY: this file has not been compiled or independently kernel-checked.
Target: Lean 4.35.0-rc2; Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55;
NYLL closure identical to canonical 8c1b16d10afaca09e0dc72753c6575e230d31a55.
-/

import Nyll.SawinTotallyRealTowers.SawinTotallyRealTower
import ExactDegreeGroup

/-!
# Exact powers-of-two arithmetic input

The public unbounded-degree theorem alone does not imply the result here.
We use its underlying infinite Galois extension, obtain a finite Galois
2-group layer, and take the fixed field of a normal subgroup of index `2^i`.
Lifting this field back into the algebraic closure preserves its actual
inclusion in the original extension. The original arithmetic theorems then
apply to that exact-degree layer, not merely to its larger parent.

The same infinite prime set is chosen before `i`. The chosen fields need
not be nested, and this file makes no nesting or coherence assertion.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open AlgebraicNumberTheory.PrimeSelection
open AlgebraicNumberTheory.DiscriminantBounds

/-- The common prime set, exact degrees, and both versions of the uniform
discriminant bound. These are separate per-degree witnesses, not a nested tower. -/
theorem sawin_totally_real_exact_degree_tower_with_discr_bound :
    ∃ Q : Set ℕ, Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ i : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        Module.finrank ℚ F = 2 ^ i ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ 255255 ∧
        |(NumberField.discr F : ℝ)| ≤ (255255 : ℝ) ^ Module.finrank ℚ F ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p := by
  classical
  let instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨primes, L, hGal, _, hInfinite, hL, hprimes, _, hsplit⟩ :=
    exists_sawinInfinite_totallyReal_split_field
  let Q : Set ℕ := Set.range (fun n : ℕ ↦ (primes n).val)
  have hQ : Q.Infinite :=
    Set.infinite_of_forall_exists_gt
      (fun a ↦ ⟨(primes a).val, ⟨a, rfl⟩, (hprimes a).1⟩)
  refine ⟨Q, hQ, ?_, ?_⟩
  · rintro q ⟨n, rfl⟩
    exact ⟨(primes n).property, (hprimes n).2.2⟩
  · intro i
    obtain ⟨E, hE, hi⟩ :=
      @AlgebraicNumberTheory.exists_finiteGaloisIntermediateField_le_finrank_ge_of_infinite_aut
        ℚ (AlgebraicClosure ℚ) _ _ _ L hGal hInfinite (2 ^ i)
    have hAdmE :=
      (isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside
        2 sawinRationalPrimeSupport E).mpr (hE.trans hL)
    obtain ⟨F, hFE, hdegree⟩ :=
      exists_finiteGalois_subfield_finrank_eq_pow_two E hAdmE.1 i hi
    have hF : F.toIntermediateField ≤ L := hFE.trans hE
    let instNumberFieldF : NumberField F := NumberField.of_module_finite ℚ F
    let instGalF : IsGalois ℚ F := F.isGalois
    have hAdmF :=
      (isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside
        2 sawinRationalPrimeSupport F).mpr (hF.trans hL)
    let instTotallyRealF : IsTotallyReal F :=
      (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal F).mp hAdmF.2.2
    have hdiscr := discr_natAbs_le_of_sawin_ramification F hAdmF.1 hAdmF.2.1
    have hroot := rootDiscr_le_of_natAbs_discr_le_pow F 255255 hdiscr
    have hdiscrReal : |(NumberField.discr F : ℝ)| ≤
        (255255 : ℝ) ^ Module.finrank ℚ F := by
      have hcast : ((NumberField.discr F).natAbs : ℝ) ≤
          (255255 : ℝ) ^ Module.finrank ℚ F := by
        exact_mod_cast hdiscr
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance,
      hdegree, ?_, hdiscrReal, ?_⟩
    · simpa only [NumberField.rootDiscr_def, Int.cast_abs, one_div, Nat.cast_ofNat] using hroot
    · rintro q ⟨n, rfl⟩
      exact exists_finset_maximalIdeals_of_finitePlaceSplitsCompletely
        F (primes n) (hsplit F hF n)

/-- Root-discriminant-only interface, matching the usual Sawin arithmetic
input with the degree strengthened from an arbitrary lower bound to `2^i`. -/
theorem sawin_totally_real_exact_degree_tower :
    ∃ Q : Set ℕ, Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ i : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        Module.finrank ℚ F = 2 ^ i ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ 255255 ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p := by
  obtain ⟨Q, hQ, hprimes, hfields⟩ := sawin_totally_real_exact_degree_tower_with_discr_bound
  refine ⟨Q, hQ, hprimes, ?_⟩
  intro i
  obtain ⟨F, instFieldF, instCharZeroF, instNumberFieldF, instTotallyRealF,
    hdegree, hroot, _, hsplit⟩ := hfields i
  exact ⟨F, instFieldF, instCharZeroF, instNumberFieldF, instTotallyRealF,
    hdegree, hroot, hsplit⟩

end ClassFieldTower.Sawin
