import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-!
# Actual quotient digits for the finite residue-vector encoding

A proved finite quotient of cardinal q is actually bijective with Fin q.
The digit encoding preserves EQUALITY and has the required range bound. It is
NOT claimed to preserve addition, multiplication, or the numeric zero label.
All linear arithmetic is done in the genuine quotient before digit encoding.

The same fixed root representative r and sign are used at both points. Equal
signed digits imply the genuine signed residue of the point difference is zero.
No CRT quotient-cardinality, split ideal product, root existence, or robust
multiplicity theorem is hidden in this encoding module.
-/

noncomputable section

namespace JSP1012.QuotientDigits

variable {R : Type*} [CommRing R]

/-- Actual finite-choice equivalence, using the proved cardinality rather than
an abstract label bound or an asserted quotient isomorphism. -/
def quotientEquivFin (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) : (R ⧸ I) ≃ Fin q := by
  letI : Fintype (R ⧸ I) := Fintype.ofFinite (R ⧸ I)
  exact Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)

def quotientDigit (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (z : R ⧸ I) : Nat :=
  (quotientEquivFin I q hcard z).val

theorem quotientDigit_lt (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (z : R ⧸ I) : quotientDigit I q hcard z < q :=
  (quotientEquivFin I q hcard z).isLt

theorem quotientDigit_injective (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) : Function.Injective (quotientDigit I q hcard) := by
  intro x y h
  apply (quotientEquivFin I q hcard).injective
  exact Fin.ext h

/-- Do not confuse the quotient's zero with numeric digit0: this is the exact
zero test valid for an arbitrary chosen finite enumeration. -/
theorem eq_zero_iff_digit_eq_zero_digit (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (z : R ⧸ I) :
    z = 0 ↔ quotientDigit I q hcard z = quotientDigit I q hcard 0 :=
  ⟨congrArg (quotientDigit I q hcard), fun h => quotientDigit_injective I q hcard h⟩

/-- True selects the plus sign; false selects the minus sign. -/
def signedLinear (I : Ideal R) (r : R) (sign : Bool) (x y : R) : R ⧸ I :=
  Ideal.Quotient.mk I x +
    if sign then Ideal.Quotient.mk I r * Ideal.Quotient.mk I y
    else -(Ideal.Quotient.mk I r * Ideal.Quotient.mk I y)

/-- Genuine quotient arithmetic, with no claimed arithmetic on the digit labels. -/
theorem signedLinear_sub (I : Ideal R) (r : R) (sign : Bool) (x y x' y' : R) :
    signedLinear I r sign (x - x') (y - y') =
      signedLinear I r sign x y - signedLinear I r sign x' y' := by
  cases sign <;> simp [signedLinear, map_sub] <;> ring

def signedDigit (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (r : R) (sign : Bool) (x y : R) : Nat :=
  quotientDigit I q hcard (signedLinear I r sign x y)

theorem signedDigit_lt (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (r : R) (sign : Bool) (x y : R) :
    signedDigit I q hcard r sign x y < q :=
  quotientDigit_lt I q hcard _

/-- Same finite residue label implies actual compatibility for the DIFFERENCE,
with the same chosen r. No condition on an unrelated fallback label is used. -/
theorem zero_difference_of_equal_signedDigits (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (r : R) (sign : Bool) (x y x' y' : R)
    (h : signedDigit I q hcard r sign x y = signedDigit I q hcard r sign x' y') :
    signedLinear I r sign (x - x') (y - y') = 0 := by
  have heq : signedLinear I r sign x y = signedLinear I r sign x' y' :=
    quotientDigit_injective I q hcard h
  rw [signedLinear_sub, heq, sub_self]

theorem equal_signedDigits_iff_zero_difference (I : Ideal R) (q : Nat) [Finite (R ⧸ I)]
    (hcard : Nat.card (R ⧸ I) = q) (r : R) (sign : Bool) (x y x' y' : R) :
    signedDigit I q hcard r sign x y = signedDigit I q hcard r sign x' y' ↔
      signedLinear I r sign (x - x') (y - y') = 0 := by
  constructor
  · exact zero_difference_of_equal_signedDigits I q hcard r sign x y x' y'
  · intro h
    rw [signedLinear_sub] at h
    exact congrArg (quotientDigit I q hcard) (sub_eq_zero.mp h)

end JSP1012.QuotientDigits

#print axioms JSP1012.QuotientDigits.quotientEquivFin
#print axioms JSP1012.QuotientDigits.quotientDigit_injective
#print axioms JSP1012.QuotientDigits.signedLinear_sub
#print axioms JSP1012.QuotientDigits.equal_signedDigits_iff_zero_difference
