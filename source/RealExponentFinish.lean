import DegreeScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit rational power saving from the integer degree bracket

STATUS: SOURCE-ONLY PREPARATION. This file has not yet been compiled.
A coordinated successful build and axiom audit are required before reporting
its declarations as verified results. No compiler was launched to prepare it.

This is only the final REAL ARITHMETIC adapter. Its integer inputs, in
particular the free-set cardinality alternative, remain explicit hypotheses.
It does not assert the number-field, prime, lattice, or sieve construction.

For B=(10*Q)^2 and B^d<=n<B^(2*d), the elementary verified inequality
B<=2^B gives n^(1/(2*B))<2^d. The large-cardinality alternative can therefore
be divided by a positive actual real power. The small alternative has square
at most n and is controlled by the exponent 1/2. Both imply the strict target
exponent 1-1/(4*B), including A=0. No logarithmic estimate is assumed.

The Std dependency DegreeScale is in ../proof/DegreeScale.lean. Its exact
source/olean must be placed on the later coordinated integration search path.
-/

noncomputable section

namespace JSP1012.RealExponentFinish

/-- An ordinary nonnegative square bound gives the actual half-power bound. -/
theorem le_half_rpow_of_sq_le {a t : ℝ} (ha : 0 ≤ a) (hsq : a ^ 2 ≤ t) :
    a ≤ t ^ (1 / 2 : ℝ) := by
  have h := Real.rpow_le_rpow (sq_nonneg a) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcancel : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
    calc
      (a ^ 2) ^ (1 / 2 : ℝ) = a ^ ((2 : ℝ) * (1 / 2)) :=
        (Real.rpow_natCast_mul ha 2 (1 / 2 : ℝ)).symm
      _ = a := by norm_num
  simpa only [hcancel] using h

/-- Taking the positive real 2B-th root of the integer upper bracket is
legitimate, and its comparison with 2^d is STRICT. -/
theorem root_lt_two_pow (B d n : ℕ) (hB : 0 < B)
    (hhi : n < B ^ (2 * d)) :
    (n : ℝ) ^ (1 / (2 * (B : ℝ))) < (2 : ℝ) ^ d := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hupper : n < 2 ^ (2 * B * d) :=
    hhi.trans_le (DegreeScale.upper_bracket_le_two_power B d)
  have hupper_real : (n : ℝ) < (2 : ℝ) ^ (2 * B * d) := by
    exact_mod_cast hupper
  have hroot := Real.rpow_lt_rpow (Nat.cast_nonneg n) hupper_real
    (show (0 : ℝ) < 1 / (2 * (B : ℝ)) by positivity)
  have hexponent :
      ((2 * B * d : ℕ) : ℝ) * (1 / (2 * (B : ℝ))) = (d : ℝ) := by
    push_cast
    field_simp [ne_of_gt hBreal]
    <;> ring
  have hcancel : ((2 : ℝ) ^ (2 * B * d)) ^ (1 / (2 * (B : ℝ))) =
      (2 : ℝ) ^ d := by
    calc
      ((2 : ℝ) ^ (2 * B * d)) ^ (1 / (2 * (B : ℝ))) =
          (2 : ℝ) ^ (((2 * B * d : ℕ) : ℝ) * (1 / (2 * (B : ℝ)))) :=
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)
          (2 * B * d) (1 / (2 * (B : ℝ)))).symm
      _ = (2 : ℝ) ^ d := by rw [hexponent, Real.rpow_natCast]
  simpa only [hcancel] using hroot

/-- The explicit rational saving is positive and at most one quarter. -/
theorem saving_bounds (B : ℕ) (hB : 0 < B) :
    0 < 1 / (4 * (B : ℝ)) ∧ 1 / (4 * (B : ℝ)) ≤ (1 / 4 : ℝ) := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hB_one : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hB))
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (by nlinarith : (4 : ℝ) ≤ 4 * (B : ℝ))

/-- In particular the half exponent is strictly below the target exponent. -/
theorem half_lt_target_exponent (B : ℕ) (hB : 0 < B) :
    (1 / 2 : ℝ) < 1 - 1 / (4 * (B : ℝ)) := by
  have hbound := (saving_bounds B hB).2
  linarith

/-- The stronger large-branch exponent is strictly below the final exponent. -/
theorem stronger_lt_target_exponent (B : ℕ) (hB : 0 < B) :
    (1 : ℝ) - 1 / (2 * (B : ℝ)) < 1 - 1 / (4 * (B : ℝ)) := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hreciprocal : 1 / (4 * (B : ℝ)) < 1 / (2 * (B : ℝ)) :=
    div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1)
      (by positivity : (0 : ℝ) < 2 * (B : ℝ))
      (by nlinarith : 2 * (B : ℝ) < 4 * (B : ℝ))
  linarith

/-- The large branch gives even the stronger power saving 1/(2B).
The proof uses actual positive real division, and does not require A>0. -/
theorem large_card_lt_stronger_rpow (B d n A : ℕ) (hB : 0 < B)
    (hn : 1 < n) (hhi : n < B ^ (2 * d)) (hA : 2 ^ d * A ≤ n) :
    (A : ℝ) < (n : ℝ) ^ (1 - 1 / (2 * (B : ℝ))) := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hnreal
  have htwo : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) d
  have hrootpos : (0 : ℝ) < (n : ℝ) ^ (1 / (2 * (B : ℝ))) :=
    Real.rpow_pos_of_pos hnpos _
  have hrootlt := root_lt_two_pow B d n hB hhi
  have hAreal : (2 : ℝ) ^ d * (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hA
  have hAdiv : (A : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ d :=
    (le_div_iff₀ htwo).mpr (by simpa only [mul_comm] using hAreal)
  calc
    (A : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ d := hAdiv
    _ < (n : ℝ) / (n : ℝ) ^ (1 / (2 * (B : ℝ))) :=
      div_lt_div_of_pos_left hnpos hrootpos hrootlt
    _ = (n : ℝ) ^ (1 - 1 / (2 * (B : ℝ))) := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]

/-- The small-branch numerical threshold is dominated by (10Q)^d for d>0. -/
theorem two_mul_pow_le_ten_mul_pow (Q d : ℕ) (hd : 0 < d) :
    2 * Q ^ d ≤ (10 * Q) ^ d := by
  have hten : 10 ^ 1 ≤ 10 ^ d :=
    Nat.pow_le_pow_right (by decide : 0 < 10) (show 1 ≤ d by omega)
  have htwo : 2 ≤ 10 ^ d := (by norm_num : 2 ≤ 10 ^ 1).trans hten
  calc
    2 * Q ^ d ≤ 10 ^ d * Q ^ d := Nat.mul_le_mul_right (Q ^ d) htwo
    _ = (10 * Q) ^ d := by rw [Nat.mul_pow]

/-- The lower degree bracket controls the SMALL branch by the actual half
power of n. The premise is weak enough to include the endpoint A=2Q^d. -/
theorem small_card_le_half_rpow (Q B d n A : ℕ) (hd : 0 < d)
    (hB : B = (10 * Q) ^ 2) (hlo : B ^ d ≤ n) (hA : A ≤ 2 * Q ^ d) :
    (A : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hthreshold := two_mul_pow_le_ten_mul_pow Q d hd
  have hsmall_sq : (2 * Q ^ d) ^ 2 ≤ n := by
    calc
      (2 * Q ^ d) ^ 2 ≤ ((10 * Q) ^ d) ^ 2 :=
        Nat.pow_le_pow_left hthreshold 2
      _ = ((10 * Q) ^ 2) ^ d := by simp only [← Nat.pow_mul, Nat.mul_comm]
      _ = B ^ d := by rw [hB]
      _ ≤ n := hlo
  have hsmall_sq_real : (((2 * Q ^ d : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast hsmall_sq
  have hhalf := le_half_rpow_of_sq_le (Nat.cast_nonneg (2 * Q ^ d)) hsmall_sq_real
  have hAreal : (A : ℝ) ≤ ((2 * Q ^ d : ℕ) : ℝ) := by exact_mod_cast hA
  exact hAreal.trans hhalf

/-- Exact rational-exponent finisher, with both integer bracket inequalities
and the actual integer cardinality alternative explicit. No A>0 is needed. -/
theorem card_lt_rpow_of_bracket (Q B d n A : ℕ) (hQ : 1 ≤ Q)
    (hB : B = (10 * Q) ^ 2) (hd : 0 < d) (hn : 1 < n)
    (hlo : B ^ d ≤ n) (hhi : n < B ^ (2 * d))
    (hcases : A < 2 * Q ^ d ∨ 2 ^ d * A ≤ n) :
    (A : ℝ) < (n : ℝ) ^ (1 - 1 / (4 * (B : ℝ))) := by
  have hQpos : 0 < Q := by omega
  have hBpos : 0 < B := by
    rw [hB]
    exact Nat.pow_pos (Nat.mul_pos (by decide : 0 < 10) hQpos)
  have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rcases hcases with hsmall | hlarge
  · exact (small_card_le_half_rpow Q B d n A hd hB hlo hsmall.le).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hnreal (half_lt_target_exponent B hBpos))
  · exact (large_card_lt_stronger_rpow B d n A hBpos hn hhi hlarge).trans
      (Real.rpow_lt_rpow_of_exponent_lt hnreal (stronger_lt_target_exponent B hBpos))

/-- Canonical form with B=(10Q)^2 inserted, ready for the degree-scale output. -/
theorem card_lt_explicit_rpow (Q d n A : ℕ) (hQ : 1 ≤ Q)
    (hd : 0 < d) (hn : 1 < n)
    (hlo : ((10 * Q) ^ 2) ^ d ≤ n)
    (hhi : n < ((10 * Q) ^ 2) ^ (2 * d))
    (hcases : A < 2 * Q ^ d ∨ 2 ^ d * A ≤ n) :
    (A : ℝ) < (n : ℝ) ^ (1 - 1 / (4 * (((10 * Q) ^ 2 : ℕ) : ℝ))) :=
  card_lt_rpow_of_bracket Q ((10 * Q) ^ 2) d n A hQ rfl hd hn hlo hhi hcases

end JSP1012.RealExponentFinish

#print axioms JSP1012.RealExponentFinish.le_half_rpow_of_sq_le
#print axioms JSP1012.RealExponentFinish.root_lt_two_pow
#print axioms JSP1012.RealExponentFinish.saving_bounds
#print axioms JSP1012.RealExponentFinish.large_card_lt_stronger_rpow
#print axioms JSP1012.RealExponentFinish.small_card_le_half_rpow
#print axioms JSP1012.RealExponentFinish.card_lt_rpow_of_bracket
#print axioms JSP1012.RealExponentFinish.card_lt_explicit_rpow
