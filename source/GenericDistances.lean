import FiniteCertificate

/-!
# True distances separated from finite candidate labels

A finite candidate enumeration need only label ELIGIBLE pairs. It must not
collapse all other distances to a fallback label and then pretend the labels
are globally injective. We instead use isosceles freeness for an arbitrary TRUE
distance type and require that equal eligible labels at one apex imply equal
true distances. This is sufficient for the actual weighted sieve, and its final
wedge is stated in true distances, not in numerical enumeration indices.

This is a further partial finite theorem, not an assertion that the required
number-field/geometric data exist.
-/

namespace JSP1012.TrueDistances
open JSP1012

/-- Equal eligible finite labels preserve true distance equality at one apex.
There is NO condition on labels of ineligible pairs or on any fallback value. -/
def RespectsAtApex {D : Type} (n : Nat) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (distance : Nat → Nat → D) : Prop :=
  ∀ i, i < n → ∀ j, j < n → ∀ k, k < n →
    eligible i j = true → eligible i k = true → label i j = label i k →
      distance i j = distance i k

/-- A fixed eligible label has at most |A| ordered pairs when TRUE distances are
isosceles-free. No global injectivity of the finite label function is assumed. -/
theorem pairFiber_le_card {D : Type} {n : Nat} {A : Nat → Bool}
    {eligible : Nat → Nat → Bool} {label : Nat → Nat → Nat}
    {distance : Nat → Nat → D}
    (heligible : Application.EligibleSelected n A eligible)
    (hrespect : RespectsAtApex n eligible label distance)
    (hfree : IsoscelesFree n A distance) (r : Nat) :
    Sieve.pairFiber n eligible label r ≤ countBelow n A := by
  apply sumBelow_le
  intro i hi
  cases hai : A i with
  | false =>
    have hz : countBelow n (fun j => eligible i j && decide (label i j = r)) = 0 := by
      apply countBelow_zero_of
      intro j hj
      cases he : eligible i j with
      | false => simp
      | true =>
        have hselected := (heligible i hi j hj he).1
        simp_all
    simpa only [hai, Bool.false_eq_true, ↓reduceIte] using Nat.le_of_eq hz
  | true =>
    have hu : countBelow n (fun j => eligible i j && decide (label i j = r)) ≤ 1 := by
      apply countBelow_le_of_unique
      intro j hj k hk hjr hkr
      have hjdata : eligible i j = true ∧ label i j = r := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hjr
      have hkdata : eligible i k = true ∧ label i k = r := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hkr
      have hjselected := heligible i hi j hj hjdata.1
      have hkselected := heligible i hi k hk hkdata.1
      by_cases heq : j = k
      · exact heq
      · have hd := hrespect i hi j hj k hk hjdata.1 hkdata.1
          (hjdata.2.trans hkdata.2.symm)
        exact False.elim (hfree i hi hai j hj hjselected.2.1 k hk hkselected.2.1
          hjselected.2.2 hkselected.2.2 heq hd)
    simpa only [hai, ↓reduceIte] using hu

/-- Weighted incidence contradicts freeness in the actual distance type. -/
theorem weighted_sieve_excludes_true_free {D : Type}
    (families n bins q : Nat) (A : Nat → Bool)
    (coset : Nat → Nat → Nat) (eligible : Nat → Nat → Bool)
    (label : Nat → Nat → Nat) (distance : Nat → Nat → D) (w : Nat → Nat)
    (hcoset : ∀ e, e < families → ∀ i, i < n → A i = true → coset e i < bins)
    (hsize : 2 * bins ≤ countBelow n A)
    (hinclude : ∀ e, e < families → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (coset e) i j = true → eligible i j = true)
    (heligible : Application.EligibleSelected n A eligible)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → label i j < q)
    (hrespect : RespectsAtApex n eligible label distance)
    (hoverlap : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      Sieve.overlap families (fun e => Fibers.sameFiber A (coset e)) i j ≤ w (label i j))
    (hmass : 2 * bins * sumBelow q w < families * countBelow n A) :
    ¬ IsoscelesFree n A distance := by
  intro hfree
  have hfiber : ∀ r, r < q → Sieve.pairFiber n eligible label r ≤ countBelow n A := by
    intro r hr
    exact pairFiber_le_card heligible hrespect hfree r
  have hsieve := Sieve.fiber_weighted_sieve families n bins q A coset eligible label w
    (countBelow n A) hcoset hsize hinclude hlabel hoverlap hfiber
  have hpos : 0 < countBelow n A := by
    by_cases hz : countBelow n A = 0
    · simp [hz] at hmass
    · omega
  have hstrict := Nat.mul_lt_mul_of_pos_left hmass hpos
  have hl : families * countBelow n A ^ 2 =
      countBelow n A * (families * countBelow n A) := by grind
  have hr : 2 * bins * (countBelow n A * sumBelow q w) =
      countBelow n A * (2 * bins * sumBelow q w) := by grind
  rw [hl, hr] at hsieve
  omega

/-- The actual conclusion is a wedge of equal TRUE distances on distinct points. -/
theorem wedge_of_not_free {D : Type} {n : Nat} {A : Nat → Bool}
    {distance : Nat → Nat → D} (h : ¬ IsoscelesFree n A distance) :
    ∃ i, i < n ∧ A i = true ∧ ∃ j, j < n ∧ A j = true ∧
      ∃ k, k < n ∧ A k = true ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ distance i j = distance i k := by
  classical
  by_cases hw : ∃ i, i < n ∧ A i = true ∧ ∃ j, j < n ∧ A j = true ∧
      ∃ k, k < n ∧ A k = true ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ distance i j = distance i k
  · exact hw
  · apply False.elim
    apply h
    intro i hi hai j hj haj k hk hak hij hik hjk heq
    exact hw ⟨i, hi, hai, j, hj, haj, k, hk, hak, hij, hik, hjk, heq⟩

/-- Integrated finite certificate with the conclusion in TRUE distances,
independent of arbitrary labels assigned to ineligible pairs. -/
theorem finite_sieve_certificate_true_distances {D : Type}
    (n k q : Nat) (A : Nat → Bool) (bases : List Nat)
    (residues : Nat → Nat → List Nat)
    (eligible : Nat → Nat → Bool) (label : Nat → Nat → Nat)
    (distance : Nat → Nat → D)
    (signData : Nat → Nat → List (Bool × Bool))
    (squareBits : Nat → List Bool) (subsetBound : Nat → Nat)
    (hresidue : ∀ e, e < 2 ^ k → ∀ i, i < n → A i = true →
      Radix.Bounded bases (residues e i))
    (hsize : 2 * bases.prod ≤ countBelow n A)
    (hinclude : ∀ e, e < 2 ^ k → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (fun a => Radix.encode bases (residues e a)) i j = true →
      eligible i j = true)
    (heligible : Application.EligibleSelected n A eligible)
    (hrespect : RespectsAtApex n eligible label distance)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → label i j < q)
    (hsignlen : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      (signData i j).length = k)
    (hcompatible : ∀ e, e < 2 ^ k → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (fun a => Radix.encode bases (residues e a)) i j = true →
      SignOverlap.compatible (signData i j) ((SignOverlap.signWords k).getD e []) = true)
    (hboth : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      SignOverlap.bothCount (signData i j) ≤ (squareBits (label i j)).countP id)
    (hsquarelen : ∀ r, r < q → (squareBits r).length = k)
    (hsubset : ∀ e, e < 2 ^ k → countBelow q
      (fun r => DivisorIncidence.subsetAllowed (squareBits r)
        ((SignOverlap.signWords k).getD e [])) ≤ subsetBound e)
    (hmass : 2 * bases.prod * sumBelow (2 ^ k) subsetBound <
      2 ^ k * countBelow n A) :
    ∃ i, i < n ∧ A i = true ∧ ∃ j, j < n ∧ A j = true ∧
      ∃ l, l < n ∧ A l = true ∧ i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
        distance i j = distance i l := by
  let coset : Nat → Nat → Nat := fun e i => Radix.encode bases (residues e i)
  let w : Nat → Nat := fun r => 2 ^ (squareBits r).countP id
  have hcoset : ∀ e, e < 2 ^ k → ∀ i, i < n → A i = true → coset e i < bases.prod := by
    intro e he i hi hai
    exact Radix.encode_lt_product (hresidue e he i hi hai)
  have hoverlap : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      Sieve.overlap (2 ^ k) (fun e => Fibers.sameFiber A (coset e)) i j ≤
        w (label i j) := by
    intro i hi j hj hel
    have hcompat : ∀ e, e < (SignOverlap.signWords k).length →
        Fibers.sameFiber A (coset e) i j = true →
        SignOverlap.compatible (signData i j) ((SignOverlap.signWords k).getD e []) = true := by
      intro e he hpair
      rw [SignOverlap.signWords_length] at he
      exact hcompatible e he i hi j hj hpair
    have hsign := SignIncidence.overlap_le_of_compatibility k signData
      (fun e => Fibers.sameFiber A (coset e)) i j (hsignlen i hi j hj hel) hcompat
    rw [SignOverlap.signWords_length] at hsign
    exact Nat.le_trans hsign (Nat.pow_le_pow_right (by decide) (hboth i hi j hj hel))
  have hweight : sumBelow q w ≤ sumBelow (2 ^ k) subsetBound :=
    DivisorIncidence.weights_bound_of_subset_counts q k squareBits subsetBound hsquarelen hsubset
  have hmass' : 2 * bases.prod * sumBelow q w < 2 ^ k * countBelow n A :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (2 * bases.prod) hweight) hmass
  have hnotfree := weighted_sieve_excludes_true_free (2 ^ k) n bases.prod q
    A coset eligible label distance w hcoset hsize hinclude heligible hlabel hrespect hoverlap hmass'
  exact wedge_of_not_free hnotfree


end JSP1012.TrueDistances

#print axioms JSP1012.TrueDistances.pairFiber_le_card
#print axioms JSP1012.TrueDistances.weighted_sieve_excludes_true_free
#print axioms JSP1012.TrueDistances.wedge_of_not_free

#print axioms JSP1012.TrueDistances.finite_sieve_certificate_true_distances
