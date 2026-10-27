import WeightedOverlap
import SignOverlap

/-!
# Indexed sign-family incidence equals explicit enumeration counting

The sieve counts natural-number family indices; the sign-overlap theorem counts
explicit Boolean words. This module proves that traversing every list index
with `getD` counts exactly the same compatible words, and hence transfers the
`2^(number of both-allowed coordinates)` bound to `Sieve.overlap`.

No list-index correspondence is postulated. The helper below works for every
finite list, every Boolean predicate, and every fallback value. This remains
only a finite combinatorial component of the EP1207 / JSP1012 program.
-/

namespace JSP1012.SignIncidence

open JSP1012 SignOverlap

/-- Move the first summand out of the end-recursive finite sum. -/
theorem sumBelow_first (n : Nat) (f : Nat → Nat) :
    sumBelow (n + 1) f = f 0 + sumBelow n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow (n + 1) f + f (n + 1) =
      f 0 + (sumBelow n (fun i => f (i + 1)) + f (n + 1))
    rw [ih]
    omega

/-- Counting actual indexed entries agrees with filtering the original list.
The fallback is irrelevant because every counted index is below the length. -/
theorem countBelow_getD {α : Type} (xs : List α) (P : α → Bool) (fallback : α) :
    countBelow xs.length (fun e => P (xs.getD e fallback)) = xs.countP P := by
  induction xs with
  | nil => simp [countBelow]
  | cons a xs ih =>
    unfold countBelow
    rw [List.length_cons, sumBelow_first]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    change (if P a then 1 else 0) +
      countBelow xs.length (fun e => P (xs.getD e fallback)) = _
    rw [ih, List.countP_cons]
    omega

/-- Exact bridge from indexing sign words to counting compatible sign vectors. -/
theorem indexed_compatible_count (k : Nat) (data : List (Bool × Bool))
    (hlen : data.length = k) :
    countBelow (signWords k).length
      (fun e => compatible data ((signWords k).getD e [])) = compatibleCount data := by
  rw [countBelow_getD]
  unfold compatibleCount
  rw [hlen]

/-- A family member is the compatibility relation for its actual enumerated word. -/
def signFamily (k : Nat) (data : Nat → Nat → List (Bool × Bool))
    (e i j : Nat) : Bool :=
  compatible (data i j) ((signWords k).getD e [])

/-- The sieve's overlap is literally the count of compatible enumerated words. -/
theorem overlap_eq_compatibleCount (k : Nat) (data : Nat → Nat → List (Bool × Bool))
    (i j : Nat) (hlen : (data i j).length = k) :
    Sieve.overlap (signWords k).length (signFamily k data) i j =
      compatibleCount (data i j) := by
  exact indexed_compatible_count k (data i j) hlen

/-- Indexed sign families therefore satisfy the required overlap factor. -/
theorem overlap_le_two_pow_both (k : Nat) (data : Nat → Nat → List (Bool × Bool))
    (i j : Nat) (hlen : (data i j).length = k) :
    Sieve.overlap (signWords k).length (signFamily k data) i j ≤
      2 ^ bothCount (data i j) := by
  rw [overlap_eq_compatibleCount k data i j hlen]
  exact compatibleCount_le_two_pow_both (data i j)

/-- The same overlap bound with the family count explicitly written as `2^k`. -/
theorem overlap_pow_le_two_pow_both (k : Nat) (data : Nat → Nat → List (Bool × Bool))
    (i j : Nat) (hlen : (data i j).length = k) :
    Sieve.overlap (2 ^ k) (signFamily k data) i j ≤ 2 ^ bothCount (data i j) := by
  simpa only [signWords_length] using overlap_le_two_pow_both k data i j hlen

/-- A geometric/coset relation need only imply sign compatibility, not equal it. -/
theorem overlap_le_of_compatibility (k : Nat)
    (data : Nat → Nat → List (Bool × Bool)) (R : Nat → Nat → Nat → Bool)
    (i j : Nat) (hlen : (data i j).length = k)
    (hcompatible : ∀ e, e < (signWords k).length → R e i j = true →
      compatible (data i j) ((signWords k).getD e []) = true) :
    Sieve.overlap (signWords k).length R i j ≤ 2 ^ bothCount (data i j) := by
  have hmono : Sieve.overlap (signWords k).length R i j ≤
      Sieve.overlap (signWords k).length (signFamily k data) i j :=
    countBelow_mono hcompatible
  exact Nat.le_trans hmono (overlap_le_two_pow_both k data i j hlen)

/-- A dead coordinate gives zero overlap in the actual indexed family. -/
theorem overlap_zero_of_dead_coordinate (k : Nat)
    (data : Nat → Nat → List (Bool × Bool)) (i j : Nat)
    (hlen : (data i j).length = k) (hdead : (false, false) ∈ data i j) :
    Sieve.overlap (signWords k).length (signFamily k data) i j = 0 := by
  rw [overlap_eq_compatibleCount k data i j hlen]
  exact compatibleCount_zero_of_dead_coordinate (data i j) hdead

/-- Three fully ambiguous coordinates give exactly eight actual indexed choices. -/
example : Sieve.overlap 8
    (signFamily 3 (fun _ _ => [(true, true), (true, true), (true, true)])) 0 1 = 8 := by
  decide

/-- Actual indexed overlap is zero if even one coordinate allows no sign. -/
example : Sieve.overlap 8
    (signFamily 3 (fun _ _ => [(true, true), (false, false), (true, false)])) 0 1 = 0 := by
  decide

/-- Default values outside the list do not affect the in-range indexing identity. -/
example : countBelow 3 (fun e => ([false, true, true].getD e false)) = 2 := by decide
example : countBelow 3 (fun e => ([false, true, true].getD e true)) = 2 := by decide

end JSP1012.SignIncidence

#print axioms JSP1012.SignIncidence.countBelow_getD
#print axioms JSP1012.SignIncidence.indexed_compatible_count
#print axioms JSP1012.SignIncidence.overlap_eq_compatibleCount
#print axioms JSP1012.SignIncidence.overlap_le_two_pow_both
#print axioms JSP1012.SignIncidence.overlap_le_of_compatibility
#print axioms JSP1012.SignIncidence.overlap_zero_of_dead_coordinate
