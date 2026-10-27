import FinitePairCount

/-!
# Exact finite-fiber partition identities

A finite set is an arbitrary Boolean mask of `0,...,n-1`. Labels are naturals
strictly below `q` on selected vertices. Theorems count ordered distinct pairs,
not unordered pairs and not pairs with the diagonal included.
-/

namespace JSP1012.Fibers

open JSP1012

theorem sum_add (n : Nat) (f g : Nat → Nat) :
    sumBelow n (fun i => f i + g i) = sumBelow n f + sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow_succ, ih]; omega

theorem sum_mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    sumBelow n (fun i => f i * c) = sumBelow n f * c := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sumBelow_succ, ih, Nat.add_mul]

theorem sum_swap (n m : Nat) (f : Nat → Nat → Nat) :
    sumBelow n (fun i => sumBelow m (fun j => f i j)) =
      sumBelow m (fun j => sumBelow n (fun i => f i j)) := by
  induction n with
  | zero =>
    apply Eq.symm
    exact sumBelow_zero_of (fun _ _ => rfl)
  | succ n ih =>
    simp only [sumBelow_succ]
    rw [ih, sum_add]

theorem sum_singleton (n v c : Nat) (hv : v < n) :
    sumBelow n (fun j => if v = j then c else 0) = c := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hvn : v = n
    · subst v
      have hz : sumBelow n (fun j => if n = j then c else 0) = 0 := by
        apply sumBelow_zero_of
        intro j hj
        have hnj : n ≠ j := by omega
        simp [hnj]
      simp [sumBelow_succ, hz]
    · have hvlt : v < n := by omega
      simp [sumBelow_succ, hvn, ih hvlt]

/-- Occupancy of fiber `j`, counting every selected vertex once. -/
def occupancy (n : Nat) (A : Nat → Bool) (label : Nat → Nat) (j : Nat) : Nat :=
  countBelow n (fun i => A i && decide (label i = j))

/-- Weighted partition of a selected finite set into its label fibers. -/
theorem weighted_partition (n q : Nat) (A : Nat → Bool) (label w : Nat → Nat)
    (hlabel : ∀ i, i < n → A i = true → label i < q) :
    sumBelow q (fun j => occupancy n A label j * w j) =
      sumBelow n (fun i => if A i then w (label i) else 0) := by
  calc
    _ = sumBelow q (fun j => sumBelow n (fun i =>
        (if A i && decide (label i = j) then 1 else 0) * w j)) := by
      apply sumBelow_congr
      intro j hj
      exact (sum_mul_right n _ (w j)).symm
    _ = sumBelow n (fun i => sumBelow q (fun j =>
        (if A i && decide (label i = j) then 1 else 0) * w j)) := sum_swap q n _
    _ = _ := by
      apply sumBelow_congr
      intro i hi
      cases hai : A i with
      | false =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        apply sumBelow_zero_of
        intro j hj
        simp
      | true =>
        have hl := hlabel i hi hai
        have heq : (fun j => (if A i && decide (label i = j) then 1 else 0) * w j) =
            (fun j => if label i = j then w (label i) else 0) := by
          funext j
          by_cases hij : label i = j
          · simp [hai, hij]
          · simp [hai, hij]
        rw [hai] at heq
        rw [heq, sum_singleton q (label i) (w (label i)) hl]
        simp

/-- The sum of the fiber occupancies is exactly the selected cardinality. -/
theorem partition (n q : Nat) (A : Nat → Bool) (label : Nat → Nat)
    (hlabel : ∀ i, i < n → A i = true → label i < q) :
    sumBelow q (occupancy n A label) = countBelow n A := by
  have h := weighted_partition n q A label (fun _ => 1) hlabel
  simpa [countBelow] using h

/-- Removing one known true index lowers the finite count by exactly one. -/
theorem count_exclude_index {n i : Nat} {P : Nat → Bool}
    (hi : i < n) (hPi : P i = true) :
    countBelow n P = countBelow n (fun j => P j && decide (j ≠ i)) + 1 := by
  have heq : sumBelow n (fun j => if P j then 1 else 0) =
      sumBelow n (fun j =>
        (if P j && decide (j ≠ i) then 1 else 0) + (if i = j then 1 else 0)) := by
    apply sumBelow_congr
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [hPi]
    · have hij : i ≠ j := Ne.symm hji
      cases hpj : P j <;> simp [hji, hij]
  rw [countBelow, heq, sum_add, sum_singleton n i 1 hi]
  rfl

/-- Two selected, distinct vertices have the same label. -/
def sameFiber (A : Nat → Bool) (label : Nat → Nat) (i j : Nat) : Bool :=
  A i && A j && decide (i ≠ j ∧ label i = label j)

theorem row_count {n i : Nat} {A : Nat → Bool} {label : Nat → Nat}
    (hi : i < n) :
    countBelow n (sameFiber A label i) =
      if A i then occupancy n A label (label i) - 1 else 0 := by
  cases hai : A i with
  | false =>
    have hz : countBelow n (sameFiber A label i) = 0 := by
      apply countBelow_zero_of
      intro j hj
      simp [sameFiber, hai]
    simpa [hai] using hz
  | true =>
    let P : Nat → Bool := fun j => A j && decide (label j = label i)
    have hPi : P i = true := by simp [P, hai]
    have hex := count_exclude_index hi hPi
    have hrel : sameFiber A label i = (fun j => P j && decide (j ≠ i)) := by
      funext j
      by_cases hij : i = j
      · subst j
        simp [sameFiber, P]
      · have hji : j ≠ i := Ne.symm hij
        by_cases hl : label i = label j
        · simp [sameFiber, P, hai, hij, hji, hl]
        · have hl' : label j ≠ label i := fun h => hl h.symm
          simp [sameFiber, P, hai, hij, hji, hl, hl']
    rw [hrel]
    have hocc : countBelow n P = occupancy n A label (label i) := rfl
    rw [hocc] at hex
    simp only [↓reduceIte]
    omega

/-- Exact identity for ordered distinct pairs in common fibers. -/
theorem pair_count (n q : Nat) (A : Nat → Bool) (label : Nat → Nat)
    (hlabel : ∀ i, i < n → A i = true → label i < q) :
    pairCount n (sameFiber A label) =
      sumBelow q (fun j => occupancy n A label j * (occupancy n A label j - 1)) := by
  calc
    _ = sumBelow n (fun i => if A i then occupancy n A label (label i) - 1 else 0) := by
      apply sumBelow_congr
      intro i hi
      exact row_count hi
    _ = _ := (weighted_partition n q A label
      (fun j => occupancy n A label j - 1) hlabel).symm

end JSP1012.Fibers

#print axioms JSP1012.Fibers.partition
#print axioms JSP1012.Fibers.pair_count
