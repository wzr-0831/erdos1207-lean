import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Real floor bins on a closed interval

A positive bin width `a` assigns the closed interval `[-X,X]` indices strictly
below `floor(2*X/a)+1`. Equal bins force separation STRICTLY less
than `a`. The added final bin retains the right endpoint when `2*X/a` is an
integer. The assumptions permit `X=0`.
-/

noncomputable section

namespace JSP1012.FloorBins

/-- Bin index after shifting the left endpoint to zero. -/
def bin (a X x : ℝ) : ℕ := Nat.floor ((x + X) / a)

/-- Number of bins, including a possible isolated right-endpoint bin. -/
def bins (a X : ℝ) : ℕ := Nat.floor (2 * X / a) + 1

/-- Closed-interval endpoints are retained, including `X=0`. -/
theorem bin_lt {a X x : ℝ} (ha : 0 < a) (hX : 0 ≤ X)
    (hxbox : x ∈ Set.Icc (-X) X) : bin a X x < bins a X := by
  -- This index bound itself only needs the upper endpoint; retain the box API.
  clear hX
  have hxle : (x + X) / a ≤ 2 * X / a := by
    apply (div_le_div_iff_of_pos_right ha).mpr
    linarith [hxbox.2]
  have hfloor := Nat.floor_mono hxle
  exact Nat.lt_succ_of_le hfloor

/-- Same bins have strict separation smaller than one full positive bin width. -/
theorem same_bin_abs_sub_lt {a X x y : ℝ} (ha : 0 < a)
    (hxbox : x ∈ Set.Icc (-X) X) (hybox : y ∈ Set.Icc (-X) X)
    (heq : bin a X x = bin a X y) : |x - y| < a := by
  have hxnonneg : 0 ≤ (x + X) / a := div_nonneg (by linarith [hxbox.1]) ha.le
  have hynonneg : 0 ≤ (y + X) / a := div_nonneg (by linarith [hybox.1]) ha.le
  have hxlo : (bin a X x : ℝ) ≤ (x + X) / a := Nat.floor_le hxnonneg
  have hylo : (bin a X y : ℝ) ≤ (y + X) / a := Nat.floor_le hynonneg
  have hxhi : (x + X) / a < (bin a X x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hyhi : (y + X) / a < (bin a X y : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxlo' := (le_div_iff₀ ha).mp hxlo
  have hylo' := (le_div_iff₀ ha).mp hylo
  have hxhi' := (div_lt_iff₀ ha).mp hxhi
  have hyhi' := (div_lt_iff₀ ha).mp hyhi
  rw [heq] at hxlo' hxhi'
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- The integer number of bins has the expected explicit real upper bound. -/
theorem bins_le_real {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) :
    (bins a X : ℝ) ≤ 1 + 2 * X / a := by
  have hnonneg : 0 ≤ 2 * X / a := div_nonneg (mul_nonneg (by norm_num) hX) ha.le
  have hfloor := Nat.floor_le hnonneg
  change ((Nat.floor (2 * X / a) + 1 : ℕ) : ℝ) ≤ 1 + 2 * X / a
  push_cast
  linarith

/-- Zero interval radius still has precisely one bin. -/
theorem bins_zero_radius (a : ℝ) : bins a 0 = 1 := by simp [bins]

theorem bin_zero_point (a : ℝ) : bin a 0 0 = 0 := by simp [bin]

end JSP1012.FloorBins

#print axioms JSP1012.FloorBins.bin_lt
#print axioms JSP1012.FloorBins.same_bin_abs_sub_lt
#print axioms JSP1012.FloorBins.bins_le_real
#print axioms JSP1012.FloorBins.bins_zero_radius
