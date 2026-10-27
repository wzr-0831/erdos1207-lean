import GenericDistances

/-!
# Direct non-strict mass bound for a finite true-distance free set

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.


The first theorem is the exact contrapositive of the verified true-distance
finite certificate. ALL residue bounds, size, inclusion, eligibility, true-
distance respect, sign, square-bit and subset-count hypotheses are retained.
There is no positive-selected-cardinality hypothesis: the empty selected set
already satisfies the non-strict conclusion.

The second theorem relates actual Nat-index traversal of ANY finite list to
its actual mapped sum, with arbitrary element universe and arbitrary fallback.
Only in-range entries are counted, so the fallback is never given a hidden
injectivity or arithmetic role. This is finite bookkeeping, not a whole-paper
or asymptotic conclusion.
-/

namespace JSP1012.FreeSetMass

open JSP1012

/-- Exact finite free-set mass bound with the full certificate semantics retained. -/
theorem finite_sieve_free_mass {D : Type}
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
    (hrespect : TrueDistances.RespectsAtApex n eligible label distance)
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
    (hfree : IsoscelesFree n A distance) :
    2 ^ k * countBelow n A ≤ 2 * bases.prod * sumBelow (2 ^ k) subsetBound := by
  by_cases hbound : 2 ^ k * countBelow n A ≤ 2 * bases.prod * sumBelow (2 ^ k) subsetBound
  · exact hbound
  · have hmass : 2 * bases.prod * sumBelow (2 ^ k) subsetBound <
        2 ^ k * countBelow n A := Nat.lt_of_not_ge hbound
    obtain ⟨i, hi, hai, j, hj, haj, l, hl, hal, hij, hil, hjl, heq⟩ :=
      TrueDistances.finite_sieve_certificate_true_distances
        n k q A bases residues eligible label distance signData squareBits subsetBound
        hresidue hsize hinclude heligible hrespect hlabel hsignlen hcompatible hboth hsquarelen hsubset hmass
    exact False.elim (hfree i hi hai j hj haj l hl hal hij hil hjl heq)


universe u

/-- Actual in-range indexing agrees with the actual list sum, in every universe. -/
theorem sumBelow_getD {α : Type u} (xs : List α) (f : α → Nat) (fallback : α) :
    sumBelow xs.length (fun e => f (xs.getD e fallback)) = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.length_cons, SignIncidence.sumBelow_first]
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons]
    rw [ih]

/-- The exact weighted sum over the ACTUAL complete sign-word enumeration. -/
theorem sumBelow_signWords (k : Nat) (f : List Bool → Nat) :
    sumBelow (2 ^ k) (fun e => f ((SignOverlap.signWords k).getD e [])) =
      ((SignOverlap.signWords k).map f).sum := by
  have h := sumBelow_getD (SignOverlap.signWords k) f []
  simpa only [SignOverlap.signWords_length] using h

end JSP1012.FreeSetMass

#print axioms JSP1012.FreeSetMass.finite_sieve_free_mass
#print axioms JSP1012.FreeSetMass.sumBelow_getD
#print axioms JSP1012.FreeSetMass.sumBelow_signWords
