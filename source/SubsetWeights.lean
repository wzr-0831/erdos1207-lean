import FinitePairCount

/-!
# Finite norm-weight expansion for LPZ26, section 3

`subsetProducts ps` enumerates every subset of the OCCURRENCES in `ps` once,
with its product as value. Repeated products are retained, as required when
distinct prime ideals have the same rational-prime norm. This is deliberately
NOT called the list of distinct natural divisors. The arithmetic and bijection
identifying these occurrence subsets with ideal divisors remains an obligation.

The reciprocal-weight identity is stated with its denominator cleared in Nat.
It needs positivity, and it never replaces division by an unproved oracle.
-/

namespace JSP1012.Weights

/-- Products of all occurrence subsets; equal numerical products keep multiplicity. -/
def subsetProducts : List Nat → List Nat
  | [] => [1]
  | p :: ps => subsetProducts ps ++ (subsetProducts ps).map (fun d => p * d)

theorem subsetProducts_length (ps : List Nat) :
    (subsetProducts ps).length = 2 ^ ps.length := by
  induction ps with
  | nil => simp [subsetProducts]
  | cons p ps ih => simp [subsetProducts, ih, Nat.pow_succ, Nat.mul_two]

/-- Every enumerated subset product is a divisor of the full product. -/
theorem subsetProduct_dvd (ps : List Nat) (d : Nat) (hd : d ∈ subsetProducts ps) :
    d ∣ ps.prod := by
  induction ps generalizing d with
  | nil =>
    have hd1 : d = 1 := by simpa [subsetProducts] using hd
    subst d
    exact Nat.dvd_refl 1
  | cons p ps ih =>
    simp only [subsetProducts, List.mem_append, List.mem_map] at hd
    rcases hd with hd | ⟨e, he, hde⟩
    · exact Nat.dvd_trans (ih d hd) (Nat.dvd_mul_left ps.prod p)
    · subst d
      obtain ⟨k, hk⟩ := ih e he
      refine ⟨k, ?_⟩
      simpa only [List.prod_cons, Nat.mul_assoc] using congrArg (fun x => p * x) hk

private theorem sum_map_mul (ps : List Nat) (f : Nat → Nat) (c : Nat) :
    (ps.map (fun x => c * f x)).sum = c * (ps.map f).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih, Nat.mul_add]

/-- Ordinary finite expansion of `prod (p+1)`, retaining occurrence multiplicity. -/
theorem subsetProducts_sum (ps : List Nat) :
    (subsetProducts ps).sum = (ps.map (fun p => p + 1)).prod := by
  induction ps with
  | nil => simp [subsetProducts]
  | cons p ps ih =>
    simp only [subsetProducts, List.sum_append, List.map_cons, List.prod_cons]
    have hm := sum_map_mul (subsetProducts ps) id p
    simp only [id_eq, List.map_id] at hm
    rw [hm, ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Cleared-denominator reciprocal expansion. No pairwise distinctness is needed:
occurrences, not distinct numerical divisor values, are being enumerated. -/
theorem reciprocal_subset_sum (ps : List Nat)
    (hpos : ∀ p, p ∈ ps → 0 < p) :
    ((subsetProducts ps).map (fun d => ps.prod / d)).sum =
      (ps.map (fun p => p + 1)).prod := by
  induction ps with
  | nil => simp [subsetProducts]
  | cons p ps ih =>
    have hp : 0 < p := hpos p (by simp)
    have hps : ∀ r, r ∈ ps → 0 < r := by
      intro r hr
      exact hpos r (by simp [hr])
    have hl : (subsetProducts ps).map (fun d => p * ps.prod / d) =
        (subsetProducts ps).map (fun d => p * (ps.prod / d)) := by
      apply List.map_congr_left
      intro d hd
      exact Nat.mul_div_assoc p (subsetProduct_dvd ps d hd)
    have hr : (subsetProducts ps).map (fun d => p * ps.prod / (p * d)) =
        (subsetProducts ps).map (fun d => ps.prod / d) := by
      apply List.map_congr_left
      intro d hd
      exact Nat.mul_div_mul_left ps.prod d hp
    simp only [subsetProducts, List.prod_cons, List.map_append, List.map_map,
      Function.comp_def, List.sum_append, List.map_cons]
    rw [hl, hr, sum_map_mul, ih hps]
    simp only [Nat.add_mul, Nat.one_mul]

/-- Repeat each block of prime norms once per embedding / split-prime factor. -/
def repeatedNorms : Nat → List Nat → List Nat
  | 0, _ => []
  | d + 1, ps => ps ++ repeatedNorms d ps

theorem repeatedNorms_product (d : Nat) (ps : List Nat) :
    (repeatedNorms d ps).prod = ps.prod ^ d := by
  induction d with
  | zero => simp [repeatedNorms]
  | succ d ih => simp [repeatedNorms, List.prod_append, ih, Nat.pow_succ, Nat.mul_comm]

theorem repeatedNorms_augmented_product (d : Nat) (ps : List Nat) :
    ((repeatedNorms d ps).map (fun p => p + 1)).prod =
      (ps.map (fun p => p + 1)).prod ^ d := by
  induction d with
  | zero => simp [repeatedNorms]
  | succ d ih =>
    simp [repeatedNorms, List.map_append, List.prod_append, ih, Nat.pow_succ, Nat.mul_comm]

theorem repeatedNorms_positive (d : Nat) (ps : List Nat)
    (hpos : ∀ p, p ∈ ps → 0 < p) :
    ∀ p, p ∈ repeatedNorms d ps → 0 < p := by
  induction d with
  | zero => simp [repeatedNorms]
  | succ d ih =>
    intro p hp
    simp only [repeatedNorms, List.mem_append] at hp
    exact hp.elim (hpos p) (ih p)

/-- The precise finite factorization behind the ideal-divisor weight sum,
clearing the common norm denominator `Q^d`. The ideal interpretation is not
silently asserted by this purely finite theorem. -/
theorem repeated_reciprocal_subset_sum (d : Nat) (ps : List Nat)
    (hpos : ∀ p, p ∈ ps → 0 < p) :
    ((subsetProducts (repeatedNorms d ps)).map (fun a => ps.prod ^ d / a)).sum =
      (ps.map (fun p => p + 1)).prod ^ d := by
  have h := reciprocal_subset_sum (repeatedNorms d ps) (repeatedNorms_positive d ps hpos)
  rw [repeatedNorms_product, repeatedNorms_augmented_product] at h
  exact h

end JSP1012.Weights

#print axioms JSP1012.Weights.subsetProduct_dvd
#print axioms JSP1012.Weights.reciprocal_subset_sum
#print axioms JSP1012.Weights.repeated_reciprocal_subset_sum

-- Distinct occurrences with equal norms must not be deduplicated.
example : JSP1012.Weights.subsetProducts [5,5] = [1,5,5,25] := by decide
example : ((JSP1012.Weights.subsetProducts [5,5]).map (fun a => 25 / a)).sum = 36 := by decide
example : ((JSP1012.Weights.subsetProducts []).map (fun a => 1 / a)).sum = 1 := by decide
