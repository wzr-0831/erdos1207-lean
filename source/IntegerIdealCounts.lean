import IdealNormPacking
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Actual ideal-box counts with an exact natural denominator

Source preparation. This specializes the PROVED real packing inequality at
radius 8*(Q*m)^2. The explicit norm equation and subset-norm bounds remain
conditions to be derived from the actual ideal-word products at application.
No divisor bijection or assumption about injectivity of numerical norms occurs.
-/

noncomputable section

namespace JSP1012.IntegerIdealCounts

open NumberField NumberFieldBox

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- Every positive subset norm N at most Q^d gives the actual LPZ candidate
count. The natural division is justified by an independently proved product
inequality, not by an untrusted integer arithmetic oracle. -/
theorem idealBox_card_le_div (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (Q m N : ℕ) (hQ : 0 < Q) (hm : 1 ≤ m) (hN : 0 < N)
    (hd : 0 < Module.finrank ℚ K)
    (hnorm : I.absNorm = Q ^ Module.finrank ℚ K * N)
    (hNle : N ≤ Q ^ Module.finrank ℚ K) :
    (idealBoxFinset I (8 * ((Q * m : ℕ) : ℝ) ^ 2)).card ≤
      (17 * Q * m ^ 2) ^ Module.finrank ℚ K / N := by
  let d := Module.finrank ℚ K
  let X : ℝ := ((Q * m : ℕ) : ℝ)
  let a : ℝ := (I.absNorm : ℝ) ^ (1 / (d : ℝ))
  have hnormpos : 0 < I.absNorm := by rw [hnorm]; exact Nat.mul_pos (Nat.pow_pos hQ) hN
  have ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast hnormpos) _
  have haPow : a ^ d = (I.absNorm : ℝ) := by
    simpa only [a, one_div] using
      Real.rpow_inv_natCast_pow (show (0 : ℝ) ≤ I.absNorm by positivity) (Nat.ne_of_gt hd)
  have hNormUpper : I.absNorm ≤ (Q ^ 2) ^ d := by
    calc
      I.absNorm = Q ^ d * N := hnorm
      _ ≤ Q ^ d * Q ^ d := Nat.mul_le_mul_left _ hNle
      _ = (Q ^ 2) ^ d := by simp only [pow_two, Nat.mul_pow]
  have haQ : a ≤ (Q : ℝ) ^ 2 := by
    apply (pow_le_pow_iff_left₀ ha.le (sq_nonneg _) (Nat.ne_of_gt hd)).mp
    rw [haPow]
    exact_mod_cast hNormUpper
  have hQm : Q ≤ Q * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q hm
  have haX : a ≤ X ^ 2 := by
    exact haQ.trans (by dsimp only [X]; exact_mod_cast Nat.pow_le_pow_left hQm 2)
  have hpack := IdealPacking.idealBoxFinset_card_le I hI
    (show (0 : ℝ) ≤ 8 * X ^ 2 by positivity)
  have hmul := mul_le_mul_of_nonneg_right hpack (pow_nonneg ha.le d)
  have hbase : (1 + 2 * (8 * X ^ 2) / a) * a = a + 16 * X ^ 2 := by
    field_simp [ne_of_gt ha]
    <;> ring
  have hscaled : ((idealBoxFinset I (8 * X ^ 2)).card : ℝ) * (I.absNorm : ℝ) ≤
      (17 * X ^ 2) ^ d := by
    calc
      _ = ((idealBoxFinset I (8 * X ^ 2)).card : ℝ) * a ^ d := by rw [haPow]
      _ ≤ (1 + 2 * (8 * X ^ 2) / a) ^ d * a ^ d := hmul
      _ = (a + 16 * X ^ 2) ^ d := by rw [← mul_pow, hbase]
      _ ≤ (17 * X ^ 2) ^ d :=
        pow_le_pow_left₀ (by positivity) (by linarith [haX]) d
  have hint : (idealBoxFinset I (8 * X ^ 2)).card * I.absNorm ≤
      (17 * (Q * m) ^ 2) ^ d := by
    dsimp only [X] at hscaled ⊢
    exact_mod_cast hscaled
  have hfactor : (17 * (Q * m) ^ 2) ^ d = Q ^ d * (17 * Q * m ^ 2) ^ d := by
    rw [← Nat.mul_pow]
    congr 1
    simp only [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hnorm, hfactor] at hint
  have hcancel : (idealBoxFinset I (8 * X ^ 2)).card * N ≤
      (17 * Q * m ^ 2) ^ d := by
    apply Nat.le_of_mul_le_mul_left (c := Q ^ d) _ (Nat.pow_pos hQ)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hint
  exact (Nat.le_div_iff_mul_le hN).mpr hcancel

end JSP1012.IntegerIdealCounts

#print axioms JSP1012.IntegerIdealCounts.idealBox_card_le_div
