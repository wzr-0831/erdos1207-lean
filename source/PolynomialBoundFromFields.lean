import FinitePolynomialConstruction
import PrimeListFromInfinite
import DegreeScale
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Eventual polynomial bound conditional on the explicit uniform field input

STATUS: SOURCE-ONLY PREPARATION. This file has not yet been compiled.
A coordinated successful build and axiom audit are required before reporting
its declarations as verified results. No compiler was launched to prepare it.

The heavy arithmetic input is an EXPLICIT theorem hypothesis, NOT a global
declaration without proof: for each i there exists an actual totally real
number field of degree exactly 2^i, uniform discriminant bound D, and complete
finite splitting data for every prime in ONE fixed infinite set Qset. The
fields do not have to be nested, and no coherent tower is assumed.

The finite prime list is selected ONCE, before n or i. Its product fixes B
and the positive saving c=1/(4B) for the entire eventual statement. Factor
finsets for a chosen field are obtained from the displayed splitting input
by actual Classical.choose, with the empty default used only OUTSIDE the
selected prime list. No extra local root, norm, lattice, or sieve assumption
is added to the final interface.

The exact-degree NYLL adapter is NOT imported or executed here. Consequently
this conditional composition is not by itself an unconditional EP1207 proof.
The invariant is the exact local FC expansion FCBoundAdapter.P 2 n.
-/

noncomputable section

namespace JSP1012.PolynomialBoundFromFields

open NumberField
open scoped Classical

/-- Actual splitting witnesses from the SAME common set form the concrete
finite family consumed by the already separated Minkowski/sieve construction.
All asserted record properties follow from the chosen witnesses' specs. -/
def splitFamilyFromCommonSet {F : Type*} [Field F] [NumberField F]
    (Qset : Set ℕ) (ps : List ℕ) (hnd : ps.Nodup)
    (hmem : ∀ q ∈ ps, q ∈ Qset) (hprime : ∀ q ∈ ps, q.Prime)
    (hmod : ∀ q ∈ ps, q % 4 = 1)
    (hsplit : ∀ q ∈ Qset, ∃ factors : Finset (Ideal (𝓞 F)),
      factors.card = Module.finrank ℚ F ∧
        ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 F) ∈ P) :
    MinkowskiResidueFamily.SplitFamily F := by
  let factors : ℕ → Finset (Ideal (𝓞 F)) := fun q =>
    if hq : q ∈ ps then Classical.choose (hsplit q (hmem q hq)) else ∅
  refine
    { ps := ps
      nodup := hnd
      prime := hprime
      mod4 := hmod
      factors := factors
      card := ?_
      maximal := ?_ }
  · intro q hq
    simpa only [factors, dif_pos hq] using
      (Classical.choose_spec (hsplit q (hmem q hq))).1
  · intro q hq
    simpa only [factors, dif_pos hq] using
      (Classical.choose_spec (hsplit q (hmem q hq))).2

/-- EVENTUAL composition from the explicit uniform exact-degree field input.
This has exactly the arithmetic input needed for the tower instantiation;
that input remains a hypothesis and is not silently introduced as an axiom. -/
theorem exists_eventual_polynomial_bound
    (D : ℕ) (hD : 0 < D) (Qset : Set ℕ) (hQset : Qset.Infinite)
    (hQprop : ∀ q ∈ Qset, q.Prime ∧ q % 4 = 1)
    (hFields : ∀ i : ℕ,
      ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        Module.finrank ℚ F = 2 ^ i ∧
        |(NumberField.discr F : ℝ)| ≤ (D : ℝ) ^ Module.finrank ℚ F ∧
        ∀ q ∈ Qset, ∃ factors : Finset (Ideal (𝓞 F)),
          factors.card = Module.finrank ℚ F ∧
            ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 F) ∈ P) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (FCBoundAdapter.P 2 n : ℝ) < (n : ℝ) ^ (1 - c) := by
  obtain ⟨ps, hnd, hmem, hprime, hmod, hamp⟩ :=
    PrimeListFromInfinite.exists_amplifying_prime_list Qset hQset hQprop D
  let r : ℕ := ps.prod
  have hrpos : 0 < r := PrimeListFromInfinite.prod_pos_of_primes ps hprime
  have hrone : 1 ≤ r := by omega
  let B : ℕ := (10 * r) ^ 2
  have hten : 10 ≤ 10 * r := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 10 hrone
  have hBhundred : 100 ≤ B := by
    dsimp only [B]
    exact Nat.pow_le_pow_left hten 2
  have hBtwo : 2 ≤ B := by omega
  have hBpos : 0 < B := by omega
  let c : ℝ := 1 / (4 * (B : ℝ))
  have hcpos : 0 < c := (RealExponentFinish.saving_bounds B hBpos).1
  refine ⟨c, hcpos, ?_⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨max B 2, ?_⟩
  intro n hn
  have hBn : B ≤ n := (Nat.le_max_left B 2).trans hn
  have htwon : 2 ≤ n := (Nat.le_max_right B 2).trans hn
  have hn_one : 1 < n := by omega
  obtain ⟨i, hlo, hhi⟩ := DegreeScale.exists_degree_bracket B hBtwo n hBn
  obtain ⟨F, instFieldF, instCharZeroF, instNumberFieldF, instTotallyRealF,
    hdegree, hdisc, hsplit⟩ := hFields i
  letI : Field F := instFieldF
  letI : CharZero F := instCharZeroF
  letI : NumberField F := instNumberFieldF
  letI : IsTotallyReal F := instTotallyRealF
  let f : MinkowskiResidueFamily.SplitFamily F :=
    splitFamilyFromCommonSet Qset ps hnd hmem hprime hmod hsplit
  have hf_ps : f.ps = ps := rfl
  have hQr : MinkowskiResidueFamily.Q f = r := rfl
  have hd : 0 < Module.finrank ℚ F := by
    rw [hdegree]
    exact Nat.pow_pos (by decide : 0 < 2)
  have hamp_f :
      (16 * D) * (17 * IntegerMinkowskiBound.augmentedProduct f) ≤
        2 ^ f.ps.length * MinkowskiResidueFamily.Q f := by
    simpa only [IntegerMinkowskiBound.augmentedProduct, MinkowskiResidueFamily.Q,
      hf_ps] using hamp
  have hlo_f :
      ((10 * MinkowskiResidueFamily.Q f) ^ 2) ^ Module.finrank ℚ F ≤ n := by
    simpa only [hQr, hdegree, B] using hlo
  have hnext : 2 ^ (i + 1) = 2 * 2 ^ i := by
    simp only [Nat.pow_succ, Nat.mul_comm]
  have hhi_f : n <
      ((10 * MinkowskiResidueFamily.Q f) ^ 2) ^ (2 * Module.finrank ℚ F) := by
    simpa only [hQr, hdegree, B, hnext] using hhi
  have hbound := FinitePolynomialConstruction.P_lt_of_split_field f D n
    hD hd hn_one hdisc hamp_f hlo_f hhi_f
  simpa only [hQr, B, c] using hbound

end JSP1012.PolynomialBoundFromFields

#print axioms JSP1012.PolynomialBoundFromFields.splitFamilyFromCommonSet
#print axioms JSP1012.PolynomialBoundFromFields.exists_eventual_polynomial_bound
