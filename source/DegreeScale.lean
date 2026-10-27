import Std

/-!
# Elementary controlled powers-of-two degree selection

The LPZ parameter argument needs only one field of degree `2^i` at a time. For
every integer n above a fixed base B>=2, this module selects i with
B^(2^i)<=n<B^(2^(i+1)). No coherent tower or real logarithm is assumed.
-/

namespace JSP1012.DegreeScale

theorem base_le_two_pow_self (B : Nat) : B ≤ 2 ^ B := by
  induction B with
  | zero => decide
  | succ B ih =>
    have hp : 0 < 2 ^ B := Nat.pow_pos (by decide)
    simp only [Nat.pow_succ, Nat.mul_two]
    omega

/-- Successive threshold scales strictly increase, with no base0/base1 exception. -/
theorem threshold_strict (B i : Nat) (hB : 2 ≤ B) :
    B ^ (2 ^ i) < B ^ (2 ^ (i + 1)) := by
  have hE : 0 < 2 ^ i := Nat.pow_pos (by decide)
  have hBpos : 0 < B := by omega
  have hm : 2 ≤ B ^ (2 ^ i) := by
    have h := Nat.pow_le_pow_right hBpos (show 1 ≤ 2 ^ i by omega)
    simp only [Nat.pow_one] at h
    omega
  have hp : 0 < B ^ (2 ^ i) := by omega
  have hsq := Nat.mul_lt_mul_of_pos_right (show 1 < B ^ (2 ^ i) by omega) hp
  have hs : B ^ (2 ^ i) < B ^ (2 ^ i) * B ^ (2 ^ i) := by simpa using hsq
  simpa only [Nat.pow_succ, Nat.pow_mul, Nat.pow_zero, Nat.one_mul, Nat.mul_one] using hs

/-- Fully quantified natural-number bracket for a controlled power-of-two degree. -/
theorem exists_degree_bracket (B : Nat) (hB : 2 ≤ B) :
    ∀ n : Nat, B ≤ n → ∃ i : Nat,
      B ^ (2 ^ i) ≤ n ∧ n < B ^ (2 ^ (i + 1)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    by_cases hprev : B ≤ n
    · obtain ⟨i, hlo, hhi⟩ := ih hprev
      by_cases hnext : n + 1 < B ^ (2 ^ (i + 1))
      · exact ⟨i, by omega, hnext⟩
      · have heq : n + 1 = B ^ (2 ^ (i + 1)) := by omega
        refine ⟨i + 1, by omega, ?_⟩
        rw [heq]
        exact threshold_strict B (i + 1) hB
    · have heq : n + 1 = B := by omega
      refine ⟨0, ?_, ?_⟩
      · simpa using hn
      · rw [heq]
        simpa using threshold_strict B 0 hB

/-- The explicit rational-exponent plan uses this integer inequality rather
than logarithms: B<=2^B bounds the next bracket by a power of two. -/
theorem upper_bracket_le_two_power (B d : Nat) :
    B ^ (2 * d) ≤ 2 ^ (2 * B * d) := by
  have h := Nat.pow_le_pow_left (base_le_two_pow_self B) (2 * d)
  simpa only [← Nat.pow_mul, Nat.mul_assoc, Nat.mul_left_comm] using h

end JSP1012.DegreeScale

#print axioms JSP1012.DegreeScale.base_le_two_pow_self
#print axioms JSP1012.DegreeScale.threshold_strict
#print axioms JSP1012.DegreeScale.exists_degree_bracket
#print axioms JSP1012.DegreeScale.upper_bracket_le_two_power
