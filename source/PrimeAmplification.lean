import Std

/-!
# Integer-only amplification from enough primes at least five

This is the exact cleared-denominator inequality needed in LPZ's parameter
choice. It does not choose primes or construct number fields: it proves the
finite product inequality once a sufficiently long list of factors >=5 is
provided. No real logarithm, limiting theorem, or optimization is used.
-/

namespace JSP1012.PrimeAmplification

/-- A deliberately loose, elementary growth estimate for the ratio 5/3. -/
theorem ratio_growth (n : Nat) : (n + 4) * 3 ^ (n + 3) ≤ 5 ^ (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hc : (n + 5) * 3 ≤ 5 * (n + 4) := by omega
    have h1 := Nat.mul_le_mul_right (3 ^ (n + 3)) hc
    have h2 := Nat.mul_le_mul_left 5 ih
    calc
      (n + 1 + 4) * 3 ^ (n + 1 + 3) = ((n + 5) * 3) * 3 ^ (n + 3) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (5 * (n + 4)) * 3 ^ (n + 3) := h1
      _ = 5 * ((n + 4) * 3 ^ (n + 3)) := Nat.mul_assoc _ _ _
      _ ≤ 5 * 5 ^ (n + 3) := h2
      _ = 5 ^ (n + 1 + 3) := by
        simp only [Nat.pow_succ, Nat.mul_comm]

theorem large_ratio (C : Nat) : C * 3 ^ (C + 3) ≤ 5 ^ (C + 3) :=
  Nat.le_trans (Nat.mul_le_mul_right _ (show C ≤ C + 4 by omega)) (ratio_growth C)

/-- Each factor p>=5 contributes 2p/(p+1)>=5/3, stated without division. -/
theorem product_ratio (ps : List Nat) (hfive : ∀ p, p ∈ ps → 5 ≤ p) :
    5 ^ ps.length * (ps.map (fun p => p + 1)).prod ≤ 6 ^ ps.length * ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : 5 ≤ p := hfive p (by simp)
    have ht : ∀ r, r ∈ ps → 5 ≤ r := by
      intro r hr
      exact hfive r (by simp [hr])
    have hc : 5 * (p + 1) ≤ 6 * p := by omega
    have h := Nat.mul_le_mul hc (ih ht)
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- At length C+3 the product amplification is at least C. Repeated numerical
factors are allowed; actual distinct-prime selection is a separate set argument. -/
theorem amplification (C : Nat) (ps : List Nat)
    (hfive : ∀ p, p ∈ ps → 5 ≤ p) (hlen : ps.length = C + 3) :
    C * (ps.map (fun p => p + 1)).prod ≤ 2 ^ ps.length * ps.prod := by
  have hg : C * 3 ^ ps.length ≤ 5 ^ ps.length := by
    rw [hlen]
    exact large_ratio C
  have h := Nat.le_trans (Nat.mul_le_mul_right (ps.map (fun p => p + 1)).prod hg)
    (product_ratio ps hfive)
  have hcancel : 3 ^ ps.length * (C * (ps.map (fun p => p + 1)).prod) ≤
      3 ^ ps.length * (2 ^ ps.length * ps.prod) := by
    change C * 3 ^ ps.length * (ps.map (fun p => p + 1)).prod ≤
      (3 * 2) ^ ps.length * ps.prod at h
    rw [Nat.mul_pow] at h
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hpos : 0 < 3 ^ ps.length := Nat.pow_pos (by decide)
  by_cases hgoal : C * (ps.map (fun p => p + 1)).prod ≤ 2 ^ ps.length * ps.prod
  · exact hgoal
  · have hstrict := Nat.mul_lt_mul_of_pos_left (show
        2 ^ ps.length * ps.prod < C * (ps.map (fun p => p + 1)).prod by omega) hpos
    omega

end JSP1012.PrimeAmplification

#print axioms JSP1012.PrimeAmplification.ratio_growth
#print axioms JSP1012.PrimeAmplification.product_ratio
#print axioms JSP1012.PrimeAmplification.amplification
