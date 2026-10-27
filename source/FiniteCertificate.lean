import MixedRadix
import DivisorIncidence
import SieveApplication

/-!
# One integrated finite LPZ sieve certificate

This theorem composes the ACTUAL coordinate labels, sign-word enumeration,
overlap bound, divisor-subset double count and isosceles-free upper bound.
There is no abstract robust multiplicity theorem among its hypotheses.

It remains a PARTIAL interface: the data and arithmetic/lattice estimates below
must be instantiated from actual number fields and planar points. This file
does not assert their existence and is not a whole EP1207 theorem.
-/

namespace JSP1012.Certificate
open JSP1012

/-- If explicit finite LPZ data pass all the listed tests, the selected vertices
contain an equal-distance wedge. Repeated-coordinate and zero-radius mistakes
cannot be hidden by a bare multiplicity assumption: eligibility requires
selected DISTINCT indices, and a geometric interpretation must still supply
an injective point enumeration and positivity on distinct points. -/
theorem finite_sieve_certificate
    (n k q : Nat) (A : Nat → Bool) (bases : List Nat)
    (residues : Nat → Nat → List Nat)
    (eligible : Nat → Nat → Bool) (distance : Nat → Nat → Nat)
    (signData : Nat → Nat → List (Bool × Bool))
    (squareBits : Nat → List Bool) (subsetBound : Nat → Nat)
    (hresidue : ∀ e, e < 2 ^ k → ∀ i, i < n → A i = true →
      Radix.Bounded bases (residues e i))
    (hsize : 2 * bases.prod ≤ countBelow n A)
    (hinclude : ∀ e, e < 2 ^ k → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (fun a => Radix.encode bases (residues e a)) i j = true →
      eligible i j = true)
    (heligible : Application.EligibleSelected n A eligible)
    (hlabel : ∀ i, i < n → ∀ j, j < n → eligible i j = true → distance i j < q)
    (hsignlen : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      (signData i j).length = k)
    (hcompatible : ∀ e, e < 2 ^ k → ∀ i, i < n → ∀ j, j < n →
      Fibers.sameFiber A (fun a => Radix.encode bases (residues e a)) i j = true →
      SignOverlap.compatible (signData i j) ((SignOverlap.signWords k).getD e []) = true)
    (hboth : ∀ i, i < n → ∀ j, j < n → eligible i j = true →
      SignOverlap.bothCount (signData i j) ≤ (squareBits (distance i j)).countP id)
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
        w (distance i j) := by
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
  have hnotfree := Application.weighted_sieve_excludes_free (2 ^ k) n bases.prod q
    A coset eligible distance w hcoset hsize hinclude heligible hlabel hoverlap hmass'
  exact Application.equal_label_wedge_of_not_free hnotfree

end JSP1012.Certificate

#print axioms JSP1012.Certificate.finite_sieve_certificate
