import PrimeSelection
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Actual finite amplification list from one fixed infinite prime set

STATUS: SOURCE-ONLY PREPARATION. This file has not yet been compiled.
A coordinated successful build and axiom audit are required before reporting
its declarations as verified results. No compiler was launched to prepare it.

The input is ONE actual infinite set Q of rational primes congruent to 1
modulo 4. Actual order-theoretic unboundedness of this same set instantiates
the verified Std selection theorem with C=272*D. No enumerated prime table,
logarithmic growth oracle, prime-density estimate, or computational selection
of a huge list is used. Every resulting member remains in that SAME Q.

D is allowed to be zero: the selection theorem itself needs no positivity
assumption. Later arithmetic applications can retain their independent D>0
hypothesis. The natural product positivity theorem also covers an empty list.

The Std dependency PrimeSelection is in ../proof/PrimeSelection.lean and
imports ../proof/PrimeAmplification.lean. These exact dependencies must be
available on the later coordinated integration search path.
-/

namespace JSP1012.PrimeListFromInfinite

/-- The actual infinite subset of naturals is unbounded in the exact argument
order expected by the verified Std finite-selection theorem. -/
theorem unbounded_of_infinite (Q : Set ℕ) (hQ : Q.Infinite) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p ∈ Q := by
  intro B
  obtain ⟨p, hpQ, hBp⟩ := hQ.exists_gt B
  exact ⟨p, hBp, hpQ⟩

/-- Stronger form retaining the exact proved length 272D+3, in addition to
distinctness, membership in the fixed infinite set, and the amplification. -/
theorem exists_amplifying_prime_list_with_length (Q : Set ℕ) (hQ : Q.Infinite)
    (hQprop : ∀ q ∈ Q, q.Prime ∧ q % 4 = 1) (D : ℕ) :
    ∃ ps : List ℕ, ps.length = 272 * D + 3 ∧ ps.Nodup ∧
      (∀ p ∈ ps, p ∈ Q) ∧ (∀ p ∈ ps, p.Prime) ∧ (∀ p ∈ ps, p % 4 = 1) ∧
      (16 * D) * (17 * (ps.map (fun p => p + 1)).prod) ≤
        2 ^ ps.length * ps.prod := by
  obtain ⟨ps, hlen, hnd, hmem, hamp⟩ :=
    PrimeSelection.exists_amplifying_list (fun p => p ∈ Q)
      (unbounded_of_infinite Q hQ) (272 * D)
  refine ⟨ps, hlen, hnd, hmem, ?_, ?_, ?_⟩
  · intro p hp
    exact (hQprop p (hmem p hp)).1
  · intro p hp
    exact (hQprop p (hmem p hp)).2
  · calc
      (16 * D) * (17 * (ps.map (fun p => p + 1)).prod) =
          (272 * D) * (ps.map (fun p => p + 1)).prod := by ring
      _ ≤ 2 ^ ps.length * ps.prod := hamp

/-- The exact LPZ amplification input, with all members drawn from the SAME
fixed infinite common split-prime set and no unproved growth assertion. -/
theorem exists_amplifying_prime_list (Q : Set ℕ) (hQ : Q.Infinite)
    (hQprop : ∀ q ∈ Q, q.Prime ∧ q % 4 = 1) (D : ℕ) :
    ∃ ps : List ℕ, ps.Nodup ∧ (∀ p ∈ ps, p ∈ Q) ∧
      (∀ p ∈ ps, p.Prime) ∧ (∀ p ∈ ps, p % 4 = 1) ∧
      (16 * D) * (17 * (ps.map (fun p => p + 1)).prod) ≤
        2 ^ ps.length * ps.prod := by
  obtain ⟨ps, _hlen, hnd, hmem, hprime, hmod, hamp⟩ :=
    exists_amplifying_prime_list_with_length Q hQ hQprop D
  exact ⟨ps, hnd, hmem, hprime, hmod, hamp⟩

/-- Product positivity follows from actual primality, not from a further
positivity assumption about the selected product. The empty case is one. -/
theorem prod_pos_of_primes (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime) :
    0 < ps.prod := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp : p.Prime := hprime p (by simp)
    have ht : ∀ q ∈ ps, q.Prime := by
      intro q hq
      exact hprime q (by simp [hq])
    simpa only [List.prod_cons] using Nat.mul_pos hp.pos (ih ht)

/-- In particular, any finite list drawn from the same prime set has positive
product; this applies directly to either existential selection theorem. -/
theorem prod_pos_of_mem (Q : Set ℕ)
    (hQprop : ∀ q ∈ Q, q.Prime ∧ q % 4 = 1) (ps : List ℕ)
    (hmem : ∀ p ∈ ps, p ∈ Q) : 0 < ps.prod :=
  prod_pos_of_primes ps (fun p hp => (hQprop p (hmem p hp)).1)

end JSP1012.PrimeListFromInfinite

#print axioms JSP1012.PrimeListFromInfinite.unbounded_of_infinite
#print axioms JSP1012.PrimeListFromInfinite.exists_amplifying_prime_list_with_length
#print axioms JSP1012.PrimeListFromInfinite.exists_amplifying_prime_list
#print axioms JSP1012.PrimeListFromInfinite.prod_pos_of_primes
#print axioms JSP1012.PrimeListFromInfinite.prod_pos_of_mem
