import Std

/-!
# Exact natural-number mass cancellation

This is only the integer algebra at the end of the finite LPZ counting
argument. No real powers, division, asymptotic theorem, number-field input,
or additional axiom is used. Cancellation uses the proved positivity of
`G^d` and `(4*D)^d`; the selected-set size `A`, radius multiplier `m`, and
ambient size `n` are allowed to be zero.
-/

namespace JSP1012.IntegerMass

private theorem scaled_mass_identity (G Q m d : Nat) :
    Q ^ d * (2 * Q ^ d * (G * m ^ 2) ^ d) =
      G ^ d * (2 * (Q * m) ^ (2 * d)) := by
  rw [Nat.pow_mul (Q * m) 2 d]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_pow,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The stronger exact inequality, before the final use of positive dimension.
Neither positivity of `Q` nor positivity of `d` is needed for this stronger step. -/
theorem four_pow_mul_le_twice (G R Q D m d A n : Nat)
    (hG : 0 < G) (hD : 0 < D)
    (hAmp : (16 * D) * G ≤ R * Q)
    (hMass : R ^ d * A ≤ 2 * Q ^ d * (G * m ^ 2) ^ d)
    (hRadius : (Q * m) ^ (2 * d) ≤ (4 * D) ^ d * n) :
    4 ^ d * A ≤ 2 * n := by
  have hAmpPow := Nat.pow_le_pow_left hAmp d
  have hMassScaled := Nat.mul_le_mul_left (Q ^ d) hMass
  have hcombined : G ^ d * ((16 * D) ^ d * A) ≤
      G ^ d * (2 * (Q * m) ^ (2 * d)) := by
    calc
      G ^ d * ((16 * D) ^ d * A) = (((16 * D) * G) ^ d) * A := by
        simp only [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (R * Q) ^ d * A := Nat.mul_le_mul_right A hAmpPow
      _ = Q ^ d * (R ^ d * A) := by
        simp only [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ Q ^ d * (2 * Q ^ d * (G * m ^ 2) ^ d) := hMassScaled
      _ = G ^ d * (2 * (Q * m) ^ (2 * d)) := scaled_mass_identity G Q m d
  have hcancelG : (16 * D) ^ d * A ≤ 2 * (Q * m) ^ (2 * d) :=
    Nat.le_of_mul_le_mul_left hcombined (Nat.pow_pos hG)
  have hfactor : (16 * D) ^ d = 4 ^ d * (4 * D) ^ d := by
    have hbase : 16 * D = 4 * (4 * D) := by omega
    rw [hbase, Nat.mul_pow]
  have hRadiusScaled := Nat.mul_le_mul_left 2 hRadius
  have hcombinedD : (4 * D) ^ d * (4 ^ d * A) ≤ (4 * D) ^ d * (2 * n) := by
    calc
      (4 * D) ^ d * (4 ^ d * A) = (16 * D) ^ d * A := by
        rw [hfactor]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 2 * (Q * m) ^ (2 * d) := hcancelG
      _ ≤ 2 * ((4 * D) ^ d * n) := hRadiusScaled
      _ = (4 * D) ^ d * (2 * n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_left hcombinedD
    (Nat.pow_pos (Nat.mul_pos (by decide) hD))

/-- Positive integer dimension supplies the exact factor two needed to turn
`4^d*A ≤ 2*n` into `2^d*A ≤ n`. -/
theorem twice_two_pow_le_four_pow (d : Nat) (hd : 0 < d) :
    2 * 2 ^ d ≤ 4 ^ d := by
  have htwo : 2 ≤ 2 ^ d := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (show 1 ≤ d from hd)
    simpa only [Nat.pow_one] using h
  have hmul := Nat.mul_le_mul_right (2 ^ d) htwo
  have hfour : 4 ^ d = 2 ^ d * 2 ^ d := by
    rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_pow]
  rw [hfour]
  exact hmul

/-- Pure natural-number finishing step, valid also for an empty selected set. -/
theorem two_pow_bound_of_four_pow_bound (d A n : Nat) (hd : 0 < d)
    (hfour : 4 ^ d * A ≤ 2 * n) : 2 ^ d * A ≤ n := by
  have hscale := Nat.mul_le_mul_right A (twice_two_pow_le_four_pow d hd)
  have htwice : 2 * (2 ^ d * A) ≤ 2 * n := by
    calc
      2 * (2 ^ d * A) = (2 * 2 ^ d) * A := by simp only [Nat.mul_assoc]
      _ ≤ 4 ^ d * A := hscale
      _ ≤ 2 * n := hfour
  exact Nat.le_of_mul_le_mul_left htwice (by decide)

/-- The requested mass-cancellation theorem, with every positive premise explicit. -/
theorem mass_cancellation (G R Q D m d A n : Nat)
    (hG : 0 < G) (hD : 0 < D) (_hQ : 0 < Q) (hd : 0 < d)
    (hAmp : (16 * D) * G ≤ R * Q)
    (hMass : R ^ d * A ≤ 2 * Q ^ d * (G * m ^ 2) ^ d)
    (hRadius : (Q * m) ^ (2 * d) ≤ (4 * D) ^ d * n) :
    2 ^ d * A ≤ n := by
  exact two_pow_bound_of_four_pow_bound d A n hd
    (four_pow_mul_le_twice G R Q D m d A n hG hD hAmp hMass hRadius)

/-- Both useful endpoint inequalities, for callers which need the stronger form. -/
theorem mass_bounds (G R Q D m d A n : Nat)
    (hG : 0 < G) (hD : 0 < D) (_hQ : 0 < Q) (hd : 0 < d)
    (hAmp : (16 * D) * G ≤ R * Q)
    (hMass : R ^ d * A ≤ 2 * Q ^ d * (G * m ^ 2) ^ d)
    (hRadius : (Q * m) ^ (2 * d) ≤ (4 * D) ^ d * n) :
    4 ^ d * A ≤ 2 * n ∧ 2 ^ d * A ≤ n := by
  have hfour := four_pow_mul_le_twice G R Q D m d A n hG hD hAmp hMass hRadius
  exact ⟨hfour, two_pow_bound_of_four_pow_bound d A n hd hfour⟩

/-- Equality case at dimension one checks every hypothesis and both conclusions. -/
example : 4 ^ 1 * 2 ≤ 2 * 4 ∧ 2 ^ 1 * 2 ≤ 4 :=
  mass_bounds 1 4 4 1 1 1 2 4
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- Zero selected size, multiplier, and ambient size are genuinely allowed. -/
example : 2 ^ 1 * 0 ≤ 0 :=
  mass_cancellation 1 16 1 1 0 1 0 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end JSP1012.IntegerMass

#print axioms JSP1012.IntegerMass.four_pow_mul_le_twice
#print axioms JSP1012.IntegerMass.twice_two_pow_le_four_pow
#print axioms JSP1012.IntegerMass.mass_cancellation
#print axioms JSP1012.IntegerMass.mass_bounds
