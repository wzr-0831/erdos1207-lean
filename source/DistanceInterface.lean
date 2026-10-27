import FinitePairCount

/-!
# Distance-label and geometric-vertex interfaces

These lemmas record the conditions needed when the finite counting core is
applied to actual geometry. An injective point enumeration is REQUIRED when
passing from point-set triangle freeness to index freeness. Injective changes
of exact distance labels preserve multiplicities; positive-radius facts are
proved from an explicit metric property, not assumed silently for an arbitrary
label function. No number-field existence or robust multiplicity bound is used.
-/

namespace JSP1012.Interface
open JSP1012

theorem sum_pos_iff (n : Nat) (f : Nat → Nat) :
    0 < sumBelow n f ↔ ∃ i, i < n ∧ 0 < f i := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    rw [sumBelow_succ]
    constructor
    · intro h
      by_cases hn : 0 < f n
      · exact ⟨n, by omega, hn⟩
      · have hs : 0 < sumBelow n f := by omega
        obtain ⟨i, hi, hfi⟩ := ih.mp hs
        exact ⟨i, by omega, hfi⟩
    · rintro ⟨i, hi, hfi⟩
      by_cases hin : i = n
      · subst i
        omega
      · have hil : i < n := by omega
        have hs := ih.mpr ⟨i, hil, hfi⟩
        omega

theorem count_pos_iff (n : Nat) (P : Nat → Bool) :
    0 < countBelow n P ↔ ∃ i, i < n ∧ P i = true := by
  rw [countBelow, sum_pos_iff]
  constructor
  · rintro ⟨i, hi, hPi⟩
    cases hval : P i with
    | false => simp [hval] at hPi
    | true => exact ⟨i, hi, hval⟩
  · rintro ⟨i, hi, hPi⟩
    exact ⟨i, hi, by simp [hPi]⟩

theorem pair_pos_iff (n : Nat) (R : Nat → Nat → Bool) :
    0 < pairCount n R ↔ ∃ i, i < n ∧ ∃ j, j < n ∧ R i j = true := by
  rw [pairCount, sum_pos_iff]
  constructor
  · rintro ⟨i, hi, hrow⟩
    obtain ⟨j, hj, hij⟩ := (count_pos_iff n (R i)).mp hrow
    exact ⟨i, hi, j, hj, hij⟩
  · rintro ⟨i, hi, j, hj, hij⟩
    exact ⟨i, hi, (count_pos_iff n (R i)).mpr ⟨j, hj, hij⟩⟩

section Geometry
variable {Point D E : Type} [DecidableEq D] [DecidableEq E]

/-- No geometric triangle among selected POINTS, rather than among indices. -/
def PointSetIsoscelesFree (S : Point → Prop) (d : Point → Point → D) : Prop :=
  ∀ x, S x → ∀ y, S y → ∀ z, S z →
    x ≠ y → x ≠ z → y ≠ z → d x y ≠ d x z

/-- The needed injectivity is only on selected indices below `n`. -/
def InjectiveOnSelected (n : Nat) (A : Nat → Bool) (p : Nat → Point) : Prop :=
  ∀ i, i < n → A i = true → ∀ j, j < n → A j = true → p i = p j → i = j

omit [DecidableEq D] in
theorem indexed_free_of_pointSet_free {n : Nat} {A : Nat → Bool}
    {S : Point → Prop} {p : Nat → Point} {d : Point → Point → D}
    (hinj : InjectiveOnSelected n A p)
    (hmem : ∀ i, i < n → A i = true → S (p i))
    (hfree : PointSetIsoscelesFree S d) :
    IsoscelesFree n A (fun i j => d (p i) (p j)) := by
  intro i hi hai j hj haj k hk hak hij hik hjk
  apply hfree (p i) (hmem i hi hai) (p j) (hmem j hj haj) (p k) (hmem k hk hak)
  · intro heq
    exact hij (hinj i hi hai j hj haj heq)
  · intro heq
    exact hik (hinj i hi hai k hk hak heq)
  · intro heq
    exact hjk (hinj j hj haj k hk hak heq)

/-- An injective relabeling cannot create or identify exact distances. -/
theorem distanceRelation_relabel (d : Nat → Nat → D) (r : D) (σ : D → E)
    (hσ : ∀ a b, σ a = σ b → a = b) :
    distanceRelation (fun i j => σ (d i j)) (σ r) = distanceRelation d r := by
  funext i j
  have heq : σ (d i j) = σ r ↔ d i j = r :=
    ⟨hσ (d i j) r, fun h => congrArg σ h⟩
  simp only [distanceRelation, heq]

theorem multiplicity_relabel (n : Nat) (A : Nat → Bool) (d : Nat → Nat → D)
    (r : D) (σ : D → E) (hσ : ∀ a b, σ a = σ b → a = b) :
    distanceMultiplicity n A (fun i j => σ (d i j)) (σ r) =
      distanceMultiplicity n A d r := by
  simp only [distanceMultiplicity, distanceRelation_relabel d r σ hσ]

omit [DecidableEq D] [DecidableEq E] in
theorem free_relabel_iff {n : Nat} {A : Nat → Bool} {d : Nat → Nat → D}
    (σ : D → E) (hσ : ∀ a b, σ a = σ b → a = b) :
    IsoscelesFree n A (fun i j => σ (d i j)) ↔ IsoscelesFree n A d := by
  constructor
  · intro h i hi hai j hj haj k hk hak hij hik hjk heq
    exact h i hi hai j hj haj k hk hak hij hik hjk (congrArg σ heq)
  · intro h i hi hai j hj haj k hk hak hij hik hjk heq
    exact h i hi hai j hj haj k hk hak hij hik hjk (hσ _ _ heq)

/-- A nonzero multiplicity supplies a genuine pair of distinct selected vertices. -/
theorem pair_of_positive_multiplicity {n : Nat} {A : Nat → Bool}
    {d : Nat → Nat → D} {r : D} (h : 0 < distanceMultiplicity n A d r) :
    ∃ i, i < n ∧ A i = true ∧ ∃ j, j < n ∧ A j = true ∧ i ≠ j ∧ d i j = r := by
  obtain ⟨i, hi, j, hj, hij⟩ := (pair_pos_iff n _).mp h
  have hdata : A i = true ∧ A j = true ∧ i ≠ j ∧ d i j = r := by
    simpa [restrictRelation, distanceRelation, Bool.and_eq_true, and_assoc] using hij
  exact ⟨i, hi, hdata.1, j, hj, hdata.2.1, hdata.2.2⟩

/-- Positivity of the attained radius is a consequence of a metric property. -/
theorem positive_radius_of_positive_multiplicity {n : Nat} {A : Nat → Bool}
    {d : Nat → Nat → D} {r : D} (Positive : D → Prop)
    (hmetric : ∀ i, i < n → A i = true → ∀ j, j < n → A j = true →
      i ≠ j → Positive (d i j))
    (h : 0 < distanceMultiplicity n A d r) : Positive r := by
  obtain ⟨i, hi, hai, j, hj, haj, hij, hdist⟩ := pair_of_positive_multiplicity h
  rw [← hdist]
  exact hmetric i hi hai j hj haj hij

end Geometry
end JSP1012.Interface

#print axioms JSP1012.Interface.indexed_free_of_pointSet_free
#print axioms JSP1012.Interface.multiplicity_relabel
#print axioms JSP1012.Interface.positive_radius_of_positive_multiplicity
