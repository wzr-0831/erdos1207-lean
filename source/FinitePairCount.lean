import Std

/-!
# Finite ordered-pair counting for the Erdős1207 / JSP1012 research program

This is a proved finite combinatorial component, NOT a formalization of the
whole geometric/asymptotic theorem. No number-field, sieve, or lattice result
is assumed as an axiom. The ambient vertices are indices below `n`; arbitrary
subsets are Boolean masks. Equal-distance pairs are ORDERED and exclude loops.
-/

namespace JSP1012

/-- Sum a natural-valued function on `0,...,n-1`. -/
def sumBelow : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumBelow n f + f n

/-- Number of true values on `0,...,n-1`. -/
def countBelow (n : Nat) (P : Nat → Bool) : Nat :=
  sumBelow n (fun i => if P i then 1 else 0)

@[simp] theorem sumBelow_zero (f : Nat → Nat) : sumBelow 0 f = 0 := rfl
@[simp] theorem sumBelow_succ (n : Nat) (f : Nat → Nat) :
    sumBelow (n + 1) f = sumBelow n f + f n := rfl
@[simp] theorem countBelow_zero (P : Nat → Bool) : countBelow 0 P = 0 := rfl
@[simp] theorem countBelow_succ (n : Nat) (P : Nat → Bool) :
    countBelow (n + 1) P = countBelow n P + if P n then 1 else 0 := rfl

theorem sumBelow_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumBelow n f = sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ, h n (by omega), ih (by
      intro i hi
      exact h i (by omega))]

theorem sumBelow_le {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i ≤ g i) : sumBelow n f ≤ sumBelow n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem sumBelow_zero_of {n : Nat} {f : Nat → Nat}
    (h : ∀ i, i < n → f i = 0) : sumBelow n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, h n (by omega), ih (fun i hi => h i (by omega))]

theorem countBelow_zero_of {n : Nat} {P : Nat → Bool}
    (h : ∀ i, i < n → P i = false) : countBelow n P = 0 := by
  apply sumBelow_zero_of
  intro i hi
  simp [h i hi]

theorem countBelow_le_of_unique {n : Nat} {P : Nat → Bool}
    (h : ∀ i, i < n → ∀ j, j < n → P i = true → P j = true → i = j) :
    countBelow n P ≤ 1 := by
  induction n with
  | zero => simp [countBelow]
  | succ n ih =>
    by_cases hn : P n = true
    · have hz : countBelow n P = 0 := by
        apply countBelow_zero_of
        intro i hi
        cases hpi : P i with
        | false => rfl
        | true =>
          have heq := h i (by omega) n (by omega) hpi hn
          omega
      simp [countBelow_succ, hn, hz]
    · have hnfalse : P n = false := by cases hv : P n <;> simp_all
      have hrec := ih (fun i hi j hj hpi hpj => h i (by omega) j (by omega) hpi hpj)
      simp [countBelow_succ, hnfalse, hrec]

/-- Ordered pairs in a Boolean relation, excluding nothing implicitly. -/
def pairCount (n : Nat) (R : Nat → Nat → Bool) : Nat :=
  sumBelow n (fun i => countBelow n (R i))

/-- At most one neighbor per row gives at most one ordered pair per vertex. -/
theorem pairCount_le_vertices {n : Nat} {R : Nat → Nat → Bool}
    (h : ∀ i, i < n → ∀ j, j < n → ∀ k, k < n →
      R i j = true → R i k = true → j = k) :
    pairCount n R ≤ n := by
  have hs := sumBelow_le (f := fun i => countBelow n (R i)) (g := fun _ => 1)
    (fun i hi => countBelow_le_of_unique (h i hi))
  have hone : sumBelow n (fun _ => 1) = n := by
    clear h hs
    induction n with
    | zero => rfl
    | succ n ih => simp [sumBelow_succ, ih]
  simpa [pairCount, hone] using hs

/-- A fully quantified finite pigeonhole conclusion, not just one numerical instance. -/
theorem two_neighbors_of_pairCount_gt {n : Nat} {R : Nat → Nat → Bool}
    (h : n < pairCount n R) :
    ∃ i, i < n ∧ ∃ j, j < n ∧ ∃ k, k < n ∧
      j ≠ k ∧ R i j = true ∧ R i k = true := by
  classical
  by_cases hex : ∃ i, i < n ∧ ∃ j, j < n ∧ ∃ k, k < n ∧
      j ≠ k ∧ R i j = true ∧ R i k = true
  · exact hex
  · have huniq : ∀ i, i < n → ∀ j, j < n → ∀ k, k < n →
        R i j = true → R i k = true → j = k := by
      intro i hi j hj k hk hij hik
      by_cases heq : j = k
      · exact heq
      · exact False.elim (hex ⟨i, hi, j, hj, k, hk, heq, hij, hik⟩)
    have := pairCount_le_vertices huniq
    omega

/-- A relation restricted to the vertices selected by the Boolean mask `A`. -/
def restrictRelation (A : Nat → Bool) (R : Nat → Nat → Bool) (i j : Nat) : Bool :=
  A i && A j && R i j

/-- An isosceles-free relation has at most `|A|` ordered pairs on every subset `A`. -/
theorem restricted_pairCount_le_card {n : Nat} {A : Nat → Bool}
    {R : Nat → Nat → Bool}
    (h : ∀ i, i < n → A i = true → ∀ j, j < n → ∀ k, k < n →
      restrictRelation A R i j = true → restrictRelation A R i k = true → j = k) :
    pairCount n (restrictRelation A R) ≤ countBelow n A := by
  apply sumBelow_le
  intro i hi
  by_cases hai : A i = true
  · have hrow := countBelow_le_of_unique (h i hi hai)
    simpa [hai] using hrow
  · have haf : A i = false := by cases hv : A i <;> simp_all
    have hz : countBelow n (restrictRelation A R i) = 0 := by
      apply countBelow_zero_of
      intro j hj
      simp [restrictRelation, haf]
    simp [hz, haf]

section Distances

variable {D : Type} [DecidableEq D]

/-- Squared distances, ordinary distances, or any other exact distance labels. -/
def distanceRelation (d : Nat → Nat → D) (r : D) (i j : Nat) : Bool :=
  decide (i ≠ j ∧ d i j = r)

/-- No three pairwise distinct selected vertices have equal distances from one apex. -/
def IsoscelesFree (n : Nat) (A : Nat → Bool) (d : Nat → Nat → D) : Prop :=
  ∀ i, i < n → A i = true → ∀ j, j < n → A j = true →
    ∀ k, k < n → A k = true →
      i ≠ j → i ≠ k → j ≠ k → d i j ≠ d i k

/-- Exact ordered-pair multiplicity of a fixed distance within `A`. -/
def distanceMultiplicity (n : Nat) (A : Nat → Bool) (d : Nat → Nat → D) (r : D) : Nat :=
  pairCount n (restrictRelation A (distanceRelation d r))

/-- The finite bound used in the LPZ26 application to isosceles-free subsets. -/
theorem distanceMultiplicity_le_card {n : Nat} {A : Nat → Bool}
    {d : Nat → Nat → D} (hfree : IsoscelesFree n A d) (r : D) :
    distanceMultiplicity n A d r ≤ countBelow n A := by
  apply restricted_pairCount_le_card
  intro i hi hai j hj k hk hij hik
  have hij' : A j = true ∧ i ≠ j ∧ d i j = r := by
    simpa [restrictRelation, distanceRelation, hai, Bool.and_eq_true] using hij
  have hik' : A k = true ∧ i ≠ k ∧ d i k = r := by
    simpa [restrictRelation, distanceRelation, hai, Bool.and_eq_true] using hik
  by_cases heq : j = k
  · exact heq
  · exact False.elim (hfree i hi hai j hj hij'.1 k hk hik'.1 hij'.2.1 hik'.2.1 heq
      (hij'.2.2.trans hik'.2.2.symm))

end Distances
end JSP1012

#print axioms JSP1012.two_neighbors_of_pairCount_gt
#print axioms JSP1012.distanceMultiplicity_le_card
