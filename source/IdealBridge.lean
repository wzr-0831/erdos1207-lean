import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import ResidueSigns
import ResidueNorm

/-!
# Mathlib field / quotient / ideal adapters for the verified Std finite core

This module does NOT assert existence of any number field, split prime ideal,
tower, lattice, or robust geometric construction. It adapts already proved
universal finite residue lemmas to actual Mathlib algebraic structures.

Uses the parent-confirmed stable official Mathlib environment. No NYLL code
or rc2 olean is imported by this adapter.
-/

namespace JSP1012.MathlibBridge

/-- Every actual field of characteristic different from two supplies the
minimal law interface used by the Std two-sign theorem. -/
theorem residueLaws (F : Type*) [CommRing F] [IsDomain F] (hchar : (1 : F) + 1 ≠ 0) :
    ResidueSigns.Laws F where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  add_neg_cancel := add_neg_cancel
  add_mul := add_mul
  one_mul := one_mul
  zero_mul := zero_mul
  no_zero_divisors := fun _ _ h => mul_eq_zero.mp h
  one_ne_zero := one_ne_zero
  two_ne_zero := hchar

/-- The one-sign theorem only needs actual commutative-ring identities. -/
theorem normLaws (F : Type*) [CommRing F] : ResidueNorm.Laws F where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  add_neg_cancel := add_neg_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  neg_mul := neg_mul
  mul_neg := mul_neg
  neg_neg := neg_neg

section IdealSquare
variable {R : Type*} [CommRing R]

/-- An explicit finite sum-of-products certificate is actual ideal-product
membership. This closes the previously flagged SquareSpan interpretation gap. -/
theorem squareSpan_mem_mul (I : Ideal R) {z : R}
    (hz : ResidueSigns.SquareSpan (fun a => a ∈ I) z) : z ∈ I * I := by
  induction hz with
  | product a b ha hb => exact Ideal.mul_mem_mul ha hb
  | add a b ha hb iha ihb => exact (I * I).add_mem iha ihb

/-- Both quotient signs force actual membership in the square of an ideal,
provided the quotient is an integral domain of odd characteristic. -/
theorem norm_mem_ideal_square_of_both_signs (I : Ideal R) [I.IsPrime]
    (hchar : (1 : R ⧸ I) + 1 ≠ 0) (x y r : R)
    (hr : (Ideal.Quotient.mk I r) * (Ideal.Quotient.mk I r) = -(1 : R ⧸ I))
    (hplus : Ideal.Quotient.mk I x + Ideal.Quotient.mk I r * Ideal.Quotient.mk I y = 0)
    (hminus : Ideal.Quotient.mk I x + -(Ideal.Quotient.mk I r * Ideal.Quotient.mk I y) = 0) :
    x ^ 2 + y ^ 2 ∈ I ^ 2 := by
  obtain ⟨hx, hy⟩ := ResidueSigns.coordinates_eq_zero_of_both_signs
    (residueLaws (R ⧸ I) hchar) _ _ _ hr hplus hminus
  have hxi : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hyi : y ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hs : ResidueSigns.SquareSpan (fun a => a ∈ I) (x * x + y * y) :=
    ResidueSigns.norm_in_squareSpan hxi hyi
  simpa only [pow_two] using squareSpan_mem_mul I hs

/-- Either sign already puts the squared norm in the ideal, without a field or
odd-characteristic assumption. -/
theorem norm_mem_ideal_of_either_sign (I : Ideal R) (x y r : R)
    (hr : (Ideal.Quotient.mk I r) * (Ideal.Quotient.mk I r) = -(1 : R ⧸ I))
    (hsign : Ideal.Quotient.mk I x + Ideal.Quotient.mk I r * Ideal.Quotient.mk I y = 0 ∨
      Ideal.Quotient.mk I x + -(Ideal.Quotient.mk I r * Ideal.Quotient.mk I y) = 0) :
    x ^ 2 + y ^ 2 ∈ I := by
  have hz := ResidueNorm.reduction_norm_zero_of_either_sign (normLaws (R ⧸ I))
    (Ideal.Quotient.mk I) (map_add _) (map_mul _) x y r hr hsign
  have hi : x * x + y * y ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
  simpa only [pow_two] using hi

end IdealSquare
end JSP1012.MathlibBridge

#print axioms JSP1012.MathlibBridge.residueLaws
#print axioms JSP1012.MathlibBridge.squareSpan_mem_mul
#print axioms JSP1012.MathlibBridge.norm_mem_ideal_square_of_both_signs
#print axioms JSP1012.MathlibBridge.norm_mem_ideal_of_either_sign
