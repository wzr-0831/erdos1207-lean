import FinitePairCount

/-!
# Finite natural-number Cauchy–Schwarz

A proved finite combinatorial component for the LPZ26 / Erdős1207 research
program. This file does not supply the number-field, tower, lattice, or sieve
parts of the full geometric result.
-/

namespace JSP1012.Cauchy

private theorem two_mul_product_le_squares (a b : Nat) :
    2 * (a * b) ≤ a * a + b * b := by
  by_cases hab : a ≤ b
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    have h2 : 2 * (a * (a + d)) = a * (a + d) + a * (a + d) := by omega
    rw [h2]
    simp only [Nat.mul_add, Nat.add_mul]
    rw [Nat.mul_comm d a]
    omega
  · have hba : b ≤ a := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
    have h2 : 2 * ((b + d) * b) = (b + d) * b + (b + d) * b := by omega
    rw [h2]
    simp only [Nat.mul_add, Nat.add_mul]
    rw [Nat.mul_comm d b]
    omega

theorem sumBelow_add (n : Nat) (f g : Nat → Nat) :
    sumBelow n (fun i => f i + g i) = sumBelow n f + sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumBelow_succ, ih]
    omega

theorem sumBelow_mul_left (n c : Nat) (f : Nat → Nat) :
    sumBelow n (fun i => c * f i) = c * sumBelow n f := by
  induction n with
  | zero => simp
  | succ n ih => simp [sumBelow_succ, ih, Nat.mul_add]

theorem sumBelow_mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    sumBelow n (fun i => f i * c) = sumBelow n f * c := by
  induction n with
  | zero => simp
  | succ n ih => simp [sumBelow_succ, ih, Nat.add_mul]

theorem sumBelow_const (n c : Nat) : sumBelow n (fun _ => c) = n * c := by
  induction n with
  | zero => simp
  | succ n ih => simp [sumBelow_succ, ih, Nat.add_mul]

/-- Finite Cauchy–Schwarz, with no positivity or boundedness restriction on `f`. -/
theorem sumBelow_sq_le_mul_sum_squares (n : Nat) (f : Nat → Nat) :
    (sumBelow n f) ^ 2 ≤ n * sumBelow n (fun i => (f i) ^ 2) := by
  have hpair :
      sumBelow n (fun i => sumBelow n (fun j => 2 * (f i * f j))) ≤
      sumBelow n (fun i => sumBelow n (fun j => f i * f i + f j * f j)) := by
    apply sumBelow_le
    intro i hi
    apply sumBelow_le
    intro j hj
    exact two_mul_product_le_squares (f i) (f j)
  have hleft : sumBelow n (fun i => sumBelow n (fun j => 2 * (f i * f j))) =
      2 * (sumBelow n f * sumBelow n f) := by
    simp only [sumBelow_mul_left, sumBelow_mul_right]
  have hright : sumBelow n (fun i => sumBelow n (fun j => f i * f i + f j * f j)) =
      n * sumBelow n (fun i => f i * f i) + n * sumBelow n (fun i => f i * f i) := by
    simp only [sumBelow_add, sumBelow_const, sumBelow_mul_left]
  rw [hleft, hright] at hpair
  have h : sumBelow n f * sumBelow n f ≤ n * sumBelow n (fun i => f i * f i) := by omega
  simpa [Nat.pow_succ] using h


/-- Number of ordered pairs of different objects lying in one bin, from occupancies. -/
def collisionSum (q : Nat) (occup : Nat → Nat) : Nat :=
  sumBelow q (fun j => occup j * (occup j - 1))

private theorem square_eq_pred_product_add (a : Nat) :
    a ^ 2 = a * (a - 1) + a := by
  cases a with
  | zero => simp
  | succ a =>
    simp only [Nat.succ_sub_one, Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul,
      Nat.mul_add, Nat.add_mul]

/-- The square-sum splits exactly into off-diagonal collisions and objects. -/
theorem sum_squares_eq_collisions_add (q : Nat) (occup : Nat → Nat) :
    sumBelow q (fun j => (occup j) ^ 2) = collisionSum q occup + sumBelow q occup := by
  calc
    sumBelow q (fun j => (occup j) ^ 2) =
        sumBelow q (fun j => occup j * (occup j - 1) + occup j) := by
      apply sumBelow_congr
      intro j hj
      exact square_eq_pred_product_add (occup j)
    _ = collisionSum q occup + sumBelow q occup := by
      exact sumBelow_add q _ _

/-- Cauchy–Schwarz after removing diagonal pairs, with no division or zero-bin issue. -/
theorem collision_cauchy (q : Nat) (occup : Nat → Nat) :
    (sumBelow q occup) ^ 2 ≤ q * collisionSum q occup + q * sumBelow q occup := by
  have h := sumBelow_sq_le_mul_sum_squares q occup
  rw [sum_squares_eq_collisions_add, Nat.mul_add] at h
  exact h

/-- Cleared-denominator lower bound on ordered off-diagonal collisions. -/
theorem collision_cauchy_sub (q : Nat) (occup : Nat → Nat) :
    (sumBelow q occup) ^ 2 - q * sumBelow q occup ≤ q * collisionSum q occup := by
  have h := collision_cauchy q occup
  omega

/-- If at least twice as many objects as bins are present, at least half of
Cauchy–Schwarz's square survives the removal of diagonal pairs. -/
theorem collision_lower_of_twice_bins_le (q : Nat) (occup : Nat → Nat)
    (hsize : 2 * q ≤ sumBelow q occup) :
    (sumBelow q occup) ^ 2 ≤ 2 * q * collisionSum q occup := by
  have h := collision_cauchy q occup
  have hprod := Nat.mul_le_mul_right (sumBelow q occup) hsize
  rw [Nat.mul_assoc] at hprod
  rw [Nat.mul_assoc]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h ⊢
  omega

end JSP1012.Cauchy

#print axioms JSP1012.Cauchy.sumBelow_sq_le_mul_sum_squares

#print axioms JSP1012.Cauchy.collision_cauchy_sub
#print axioms JSP1012.Cauchy.collision_lower_of_twice_bins_le

/-! Boundary checks: zero bins; equality at two objects per bin; necessity of
keeping the size hypothesis in the diagonal-removal lower bound. -/
example : JSP1012.Cauchy.collisionSum 0 (fun _ => 100) = 0 := rfl
example : JSP1012.Cauchy.collisionSum 3 (fun _ => 2) = 6 := by decide
example : (JSP1012.sumBelow 3 (fun _ => 2)) ^ 2 =
    2 * 3 * JSP1012.Cauchy.collisionSum 3 (fun _ => 2) := by decide
example : ¬ ((JSP1012.sumBelow 1 (fun _ => 1)) ^ 2 ≤
    2 * 1 * JSP1012.Cauchy.collisionSum 1 (fun _ => 1)) := by decide
