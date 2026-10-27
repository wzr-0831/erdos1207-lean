import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Prime-cardinality residue fields contain a square root of minus one

STATUS: SOURCE-ONLY PREPARATION. This version has not yet been compiled.
No Lean process was launched while preparing this module; a coordinated
Mathlib build lane and its actual successful log are still required.

For an actual finite field whose cardinality is a prime `p ≡ 1 (mod 4)`, the
root and the odd-characteristic condition are derived, not assumed. The root
uses `FiniteField.isSquare_neg_one_iff`; characteristic equals the prime
cardinality because that cardinality casts to zero. The quotient adapters
still require the ACTUAL quotient-cardinality identity as an explicit input.
No complete-splitting or quotient-cardinality theorem is postulated here.
-/

namespace JSP1012.PrimeResidue

/-- A finite field of prime cardinality has exactly that characteristic. -/
theorem ringChar_eq_of_prime_card (F : Type*) [Field F] [Fintype F]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card F = p) : ringChar F = p := by
  apply CharP.ringChar_of_prime_eq_zero hp
  rw [← hcard]
  exact FiniteField.cast_card_eq_zero F

/-- Actual finite-field arithmetic supplies both pieces required by the
one-sign and two-sign quotient lemmas. -/
theorem exists_root_and_two_ne_zero_of_card (F : Type*) [Field F] [Fintype F]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card F = p) (hmod : p % 4 = 1) :
    ∃ r : F, r * r = -(1 : F) ∧ (1 : F) + 1 ≠ 0 := by
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    exact (by decide : ¬ ((2 : ℕ) % 4 = 1)) (hp2 ▸ hmod)
  have hchar : ringChar F ≠ 2 := by
    rw [ringChar_eq_of_prime_card F hp hcard]
    exact hp_ne_two
  have htwo : (1 : F) + 1 ≠ 0 := by
    simpa only [one_add_one_eq_two] using (Ring.two_ne_zero hchar : (2 : F) ≠ 0)
  have hsquare : IsSquare (-1 : F) := by
    apply FiniteField.isSquare_neg_one_iff.mpr
    rw [hcard, hmod]
    decide
  obtain ⟨r, hr⟩ := hsquare
  exact ⟨r, hr.symm, htwo⟩

/-- `Nat.card` form, independent of the choice of finite enumeration. -/
theorem exists_root_and_two_ne_zero_of_natCard (F : Type*) [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p) (hmod : p % 4 = 1) :
    ∃ r : F, r * r = -(1 : F) ∧ (1 : F) + 1 ≠ 0 := by
  letI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = p := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact exists_root_and_two_ne_zero_of_card F hp hcard' hmod

/-- An actual maximal-ideal quotient with known prime cardinality has the
required residue root. The missing cardinality bridge is NOT hidden here. -/
theorem quotient_exists_root_of_card {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsMaximal] [Fintype (R ⧸ I)]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card (R ⧸ I) = p) (hmod : p % 4 = 1) :
    ∃ r : R ⧸ I, r * r = -(1 : R ⧸ I) ∧ (1 : R ⧸ I) + 1 ≠ 0 := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  exact exists_root_and_two_ne_zero_of_card (R ⧸ I) hp hcard hmod

/-- Quotient adapter using the enumeration-independent actual cardinality. -/
theorem quotient_exists_root_of_natCard {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (R ⧸ I) = p) (hmod : p % 4 = 1) :
    ∃ r : R ⧸ I, r * r = -(1 : R ⧸ I) ∧ (1 : R ⧸ I) + 1 ≠ 0 := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  exact exists_root_and_two_ne_zero_of_natCard (R ⧸ I) hp hcard hmod

end JSP1012.PrimeResidue

#print axioms JSP1012.PrimeResidue.ringChar_eq_of_prime_card
#print axioms JSP1012.PrimeResidue.exists_root_and_two_ne_zero_of_card
#print axioms JSP1012.PrimeResidue.exists_root_and_two_ne_zero_of_natCard
#print axioms JSP1012.PrimeResidue.quotient_exists_root_of_natCard
