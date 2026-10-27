import SignIncidence

/-!
# Exchanging the finite divisor-weight and candidate sums

For each candidate label, `bits` records which distinct PRIME-IDEAL COORDINATES
would have the extra square-divisibility property. A Boolean word selects a
subset of these coordinates. We prove that the number of allowed subsets is
exactly `2^(number of true bits)`, then exchange the candidate and subset sums.

No assertion here identifies the coordinates with actual prime ideals, proves
norm multiplicativity, or constructs the relevant lattice. In particular,
coordinates with equal norms are not merged.
-/

namespace JSP1012.DivisorIncidence
open JSP1012

/-- Not selecting a coordinate is always allowed; selecting it requires its bit. -/
def subsetData (bits : List Bool) : List (Bool × Bool) :=
  bits.map (fun b => (true, b))

def subsetAllowed (bits word : List Bool) : Bool :=
  SignOverlap.compatible (subsetData bits) word

/-- Actual allowed subsets, with no repeated sign word in the enumeration. -/
theorem subset_count (bits : List Bool) :
    SignOverlap.compatibleCount (subsetData bits) = 2 ^ bits.countP id := by
  induction bits with
  | nil => decide
  | cons b bits ih =>
    change SignOverlap.compatibleCount ((true, b) :: subsetData bits) = _
    rw [SignOverlap.compatibleCount_cons, ih]
    cases b <;> simp [Nat.pow_succ] <;> omega

/-- Exact indexed subset counting; all indices run over the complete Boolean
word enumeration proved complete and duplicate-free in SignOverlap. -/
theorem indexed_subset_count (k : Nat) (bits : List Bool) (hlen : bits.length = k) :
    countBelow (2 ^ k) (fun e => subsetAllowed bits ((SignOverlap.signWords k).getD e [])) =
      2 ^ bits.countP id := by
  have hdata : (subsetData bits).length = k := by simpa [subsetData] using hlen
  have h := SignIncidence.indexed_compatible_count k (subsetData bits) hdata
  rw [SignOverlap.signWords_length, subset_count] at h
  exact h

/-- The exact finite double-counting identity used to replace the sum of
`2^w(r)` by a sum of candidate counts indexed by ideal-divisor subsets. -/
theorem weights_exchange (candidates k : Nat) (bits : Nat → List Bool)
    (hlen : ∀ r, r < candidates → (bits r).length = k) :
    sumBelow candidates (fun r => 2 ^ (bits r).countP id) =
      sumBelow (2 ^ k) (fun e => countBelow candidates
        (fun r => subsetAllowed (bits r) ((SignOverlap.signWords k).getD e []))) := by
  calc
    _ = sumBelow candidates (fun r => countBelow (2 ^ k)
        (fun e => subsetAllowed (bits r) ((SignOverlap.signWords k).getD e []))) := by
      apply sumBelow_congr
      intro r hr
      exact (indexed_subset_count k (bits r) (hlen r hr)).symm
    _ = _ := Fibers.sum_swap candidates (2 ^ k) _

/-- Per-subset lattice/candidate estimates, once separately proved, may be
summed without an additional sieve hypothesis. -/
theorem weights_bound_of_subset_counts (candidates k : Nat) (bits : Nat → List Bool)
    (bound : Nat → Nat)
    (hlen : ∀ r, r < candidates → (bits r).length = k)
    (hcount : ∀ e, e < 2 ^ k → countBelow candidates
      (fun r => subsetAllowed (bits r) ((SignOverlap.signWords k).getD e [])) ≤ bound e) :
    sumBelow candidates (fun r => 2 ^ (bits r).countP id) ≤ sumBelow (2 ^ k) bound := by
  rw [weights_exchange candidates k bits hlen]
  exact sumBelow_le hcount

end JSP1012.DivisorIncidence

#print axioms JSP1012.DivisorIncidence.subset_count
#print axioms JSP1012.DivisorIncidence.weights_exchange
#print axioms JSP1012.DivisorIncidence.weights_bound_of_subset_counts

example : JSP1012.SignOverlap.compatibleCount
    (JSP1012.DivisorIncidence.subsetData [true, false, true]) = 4 := by decide
