import Std

/-!
# Integer Q-multiple radius without real roots or ceilings

For Q>0,e>0 and N>=Q^e, a genuine integer multiple X=Q*m satisfies
N<=X^e<=2^e*N. The proof constructs a natural power bracket by induction,
then rounds one step upwards. The LPZ specialization e=2d,N=D^d*n yields
D^d*n<=X^(2d)<=(4D)^d*n, with no real logarithm, root or ceiling parameter.
-/

namespace JSP1012.IntegerRadius

private theorem pow_strict {a b e : Nat} (hab : a < b) (he : 0 < e) : a ^ e < b ^ e := by
  cases e with
  | zero => omega
  | succ k =>
    have hb : 0 < b := by omega
    have h1 := Nat.mul_le_mul_right a (Nat.pow_le_pow_left (Nat.le_of_lt hab) k)
    have h2 := Nat.mul_lt_mul_of_pos_left hab (show 0 < b ^ k from Nat.pow_pos hb)
    exact Nat.lt_of_le_of_lt h1 h2

private theorem threshold_strict (Q e r : Nat) (hQ : 0 < Q) (he : 0 < e) :
    (Q * r) ^ e < (Q * (r + 1)) ^ e :=
  pow_strict (Nat.mul_lt_mul_of_pos_left (show r < r + 1 by omega) hQ) he

/-- The fully quantified integer power bracket; all zero-scale exceptions are explicit. -/
theorem exists_power_bracket (Q e : Nat) (hQ : 0 < Q) (he : 0 < e) :
    ∀ N : Nat, Q ^ e ≤ N → ∃ r : Nat, 1 ≤ r ∧
      (Q * r) ^ e ≤ N ∧ N < (Q * (r + 1)) ^ e := by
  intro N
  induction N with
  | zero =>
    intro hN
    have hp : 0 < Q ^ e := Nat.pow_pos hQ
    omega
  | succ N ih =>
    intro hN
    by_cases hprev : Q ^ e ≤ N
    · obtain ⟨r, hr, hlo, hhi⟩ := ih hprev
      by_cases hnext : N + 1 < (Q * (r + 1)) ^ e
      · exact ⟨r, hr, by omega, hnext⟩
      · have heq : N + 1 = (Q * (r + 1)) ^ e := by omega
        refine ⟨r + 1, by omega, by omega, ?_⟩
        rw [heq]
        exact threshold_strict Q e (r + 1) hQ he
    · have heq : N + 1 = Q ^ e := by omega
      refine ⟨1, by decide, ?_, ?_⟩
      · simpa only [Nat.mul_one] using hN
      · rw [heq]
        simpa only [Nat.mul_one] using threshold_strict Q e 1 hQ he

/-- Round one step above the bracket. The multiplicative loss is at most2^e. -/
theorem exists_multiple_radius (Q e N : Nat) (hQ : 0 < Q) (he : 0 < e)
    (hN : Q ^ e ≤ N) : ∃ m : Nat, 1 ≤ m ∧
      N ≤ (Q * m) ^ e ∧ (Q * m) ^ e ≤ 2 ^ e * N := by
  obtain ⟨r, hr, hlo, hhi⟩ := exists_power_bracket Q e hQ he N hN
  refine ⟨r + 1, by omega, Nat.le_of_lt hhi, ?_⟩
  have hm : Q * (r + 1) ≤ 2 * (Q * r) := by
    have h := Nat.mul_le_mul_left Q (show r + 1 ≤ 2 * r by omega)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  calc
    (Q * (r + 1)) ^ e ≤ (2 * (Q * r)) ^ e := Nat.pow_le_pow_left hm e
    _ = 2 ^ e * (Q * r) ^ e := Nat.mul_pow _ _ _
    _ ≤ 2 ^ e * N := Nat.mul_le_mul_left _ hlo

/-- The exact integer-radius interface for the LPZ counting construction. -/
theorem exists_integer_radius (Q D d n : Nat) (hQ : 0 < Q) (_hD : 0 < D)
    (hd : 0 < d) (hN : Q ^ (2 * d) ≤ D ^ d * n) :
    ∃ m : Nat, 1 ≤ m ∧ D ^ d * n ≤ (Q * m) ^ (2 * d) ∧
      (Q * m) ^ (2 * d) ≤ (4 * D) ^ d * n := by
  obtain ⟨m, hm, hlo, hhi⟩ := exists_multiple_radius Q (2 * d) (D ^ d * n) hQ (by omega) hN
  have h4 : 2 ^ (2 * d) = 4 ^ d := by rw [Nat.pow_mul]
  refine ⟨m, hm, hlo, ?_⟩
  simpa only [h4, Nat.mul_pow, Nat.mul_assoc] using hhi

/-- The degree-scale bracket already supplies the needed lower threshold. -/
theorem exists_integer_radius_of_bracket (Q D d n : Nat) (hQ : 0 < Q) (hD : 0 < D)
    (hd : 0 < d) (hlarge : ((10 * Q) ^ 2) ^ d ≤ n) :
    ∃ m : Nat, 1 ≤ m ∧ D ^ d * n ≤ (Q * m) ^ (2 * d) ∧
      (Q * m) ^ (2 * d) ≤ (4 * D) ^ d * n := by
  apply exists_integer_radius Q D d n hQ hD hd
  have hpow : Q ^ (2 * d) ≤ ((10 * Q) ^ 2) ^ d := by
    have h := Nat.pow_le_pow_left (show Q ≤ 10 * Q by omega) (2 * d)
    simpa only [Nat.pow_mul] using h
  have hDpow : 1 ≤ D ^ d := by have h : 0 < D ^ d := Nat.pow_pos hD; omega
  have hn : n ≤ D ^ d * n := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hDpow
  exact Nat.le_trans (Nat.le_trans hpow hlarge) hn

end JSP1012.IntegerRadius

#print axioms JSP1012.IntegerRadius.exists_power_bracket
#print axioms JSP1012.IntegerRadius.exists_integer_radius_of_bracket
