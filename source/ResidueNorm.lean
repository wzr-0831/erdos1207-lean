import Std

/-!
# Generic residue one-sign norm implication

The explicit law data below consists only of commutative-ring identities used
in the proof. There is no domain, odd-characteristic, orderedness, or cardinality
assumption: one sign already forces the squared norm to vanish in any
commutative ring when `r*r = -1`.

All laws and reduction-map properties are universally quantified hypotheses,
not global axioms. No number field, quotient, prime ideal, reduction map, or
ring-law instance is asserted to exist by this module.
-/

namespace JSP1012.ResidueNorm

universe u v

/-- The exact elementary commutative-ring identities used below. This is a
law interface, not an assertion that these fields axiomatize a full ring. -/
structure Laws (F : Type u) [Add F] [Mul F] [Neg F] [Zero F] [One F] : Prop where
  add_assoc : ∀ a b c : F, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : F, a + b = b + a
  zero_add : ∀ a : F, 0 + a = a
  add_zero : ∀ a : F, a + 0 = a
  add_neg_cancel : ∀ a : F, a + -a = 0
  mul_assoc : ∀ a b c : F, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : F, a * b = b * a
  one_mul : ∀ a : F, 1 * a = a
  neg_mul : ∀ a b : F, (-a) * b = -(a * b)
  mul_neg : ∀ a b : F, a * (-b) = -(a * b)
  neg_neg : ∀ a : F, -(-a) = a

section RingIdentities

variable {F : Type u} [Add F] [Mul F] [Neg F] [Zero F] [One F]
variable (laws : Laws F)
include laws

/-- Squaring a negative element removes its sign. -/
theorem square_neg (a : F) : (-a) * (-a) = a * a := by
  calc
    (-a) * (-a) = -(a * (-a)) := laws.neg_mul a (-a)
    _ = -(-(a * a)) := congrArg (fun z => -z) (laws.mul_neg a a)
    _ = a * a := laws.neg_neg (a * a)

/-- Square of a product, derived from the actual associativity/commutativity laws. -/
theorem square_product (a b : F) : (a * b) * (a * b) = (a * a) * (b * b) := by
  calc
    (a * b) * (a * b) = a * (b * (a * b)) := laws.mul_assoc a b (a * b)
    _ = a * ((b * a) * b) :=
      congrArg (fun z => a * z) (laws.mul_assoc b a b).symm
    _ = a * ((a * b) * b) :=
      congrArg (fun z => a * (z * b)) (laws.mul_comm b a)
    _ = a * (a * (b * b)) :=
      congrArg (fun z => a * z) (laws.mul_assoc a b b)
    _ = (a * a) * (b * b) := (laws.mul_assoc a a (b * b)).symm

/-- The root relation alone makes the sum of the two relevant squares zero. -/
theorem root_mul_norm_zero (r y : F) (hr : r * r = -(1 : F)) :
    (r * y) * (r * y) + y * y = 0 := by
  calc
    (r * y) * (r * y) + y * y = (r * r) * (y * y) + y * y :=
      congrArg (fun z => z + y * y) (square_product laws r y)
    _ = (-(1 : F)) * (y * y) + y * y :=
      congrArg (fun z => z * (y * y) + y * y) hr
    _ = -((1 : F) * (y * y)) + y * y :=
      congrArg (fun z => z + y * y) (laws.neg_mul 1 (y * y))
    _ = -(y * y) + y * y :=
      congrArg (fun z => -z + y * y) (laws.one_mul (y * y))
    _ = y * y + -(y * y) := laws.add_comm (-(y * y)) (y * y)
    _ = 0 := laws.add_neg_cancel (y * y)

/-- One plus sign makes the squared norm vanish, in arbitrary characteristic. -/
theorem norm_zero_of_plus_sign (x y r : F) (hr : r * r = -(1 : F))
    (hplus : x + r * y = 0) : x * x + y * y = 0 := by
  have hx : x = -(r * y) := by
    calc
      x = (x + r * y) + -(r * y) := by
        rw [laws.add_assoc, laws.add_neg_cancel, laws.add_zero]
      _ = 0 + -(r * y) := congrArg (fun z => z + -(r * y)) hplus
      _ = -(r * y) := laws.zero_add _
  calc
    x * x + y * y = (-(r * y)) * (-(r * y)) + y * y := by rw [hx]
    _ = (r * y) * (r * y) + y * y :=
      congrArg (fun z => z + y * y) (square_neg laws (r * y))
    _ = 0 := root_mul_norm_zero laws r y hr

/-- One minus sign likewise makes the squared norm vanish. -/
theorem norm_zero_of_minus_sign (x y r : F) (hr : r * r = -(1 : F))
    (hminus : x + -(r * y) = 0) : x * x + y * y = 0 := by
  have hx : x = r * y := by
    calc
      x = (x + -(r * y)) + r * y := by
        rw [laws.add_assoc, laws.add_comm (-(r * y)) (r * y),
          laws.add_neg_cancel, laws.add_zero]
      _ = 0 + r * y := congrArg (fun z => z + r * y) hminus
      _ = r * y := laws.zero_add _
  rw [hx]
  exact root_mul_norm_zero laws r y hr

theorem norm_zero_of_either_sign (x y r : F) (hr : r * r = -(1 : F))
    (hsign : x + r * y = 0 ∨ x + -(r * y) = 0) : x * x + y * y = 0 := by
  cases hsign with
  | inl h => exact norm_zero_of_plus_sign laws x y r hr h
  | inr h => exact norm_zero_of_minus_sign laws x y r hr h

end RingIdentities

section ReductionMap

variable {R : Type v} [Add R] [Mul R]
variable {F : Type u} [Add F] [Mul F] [Neg F] [Zero F] [One F]

/-- Actual map-add and map-mul laws transfer residue norm vanishing to membership
in the reduction kernel. There is no postulated norm-preservation equality. -/
theorem reduction_norm_zero_of_either_sign (laws : Laws F) (reduction : R → F)
    (map_add : ∀ a b, reduction (a + b) = reduction a + reduction b)
    (map_mul : ∀ a b, reduction (a * b) = reduction a * reduction b)
    (x y r : R) (hr : reduction r * reduction r = -(1 : F))
    (hsign : reduction x + reduction r * reduction y = 0 ∨
      reduction x + -(reduction r * reduction y) = 0) :
    reduction (x * x + y * y) = 0 := by
  rw [map_add, map_mul, map_mul]
  exact norm_zero_of_either_sign laws (reduction x) (reduction y) (reduction r) hr hsign

/-- Source-level plus-sign kernel membership, with its reduction derived using
the specified actual map laws. -/
theorem reduction_norm_zero_of_plus_kernel (laws : Laws F) (reduction : R → F)
    (map_add : ∀ a b, reduction (a + b) = reduction a + reduction b)
    (map_mul : ∀ a b, reduction (a * b) = reduction a * reduction b)
    (x y r : R) (hr : reduction r * reduction r = -(1 : F))
    (hplus : reduction (x + r * y) = 0) : reduction (x * x + y * y) = 0 := by
  have hplus' : reduction x + reduction r * reduction y = 0 := by
    rw [map_add, map_mul] at hplus
    exact hplus
  exact reduction_norm_zero_of_either_sign laws reduction map_add map_mul x y r hr
    (Or.inl hplus')

/-- Source-level minus-sign kernel membership needs the actual map-neg law too. -/
theorem reduction_norm_zero_of_minus_kernel [Neg R]
    (laws : Laws F) (reduction : R → F)
    (map_add : ∀ a b, reduction (a + b) = reduction a + reduction b)
    (map_mul : ∀ a b, reduction (a * b) = reduction a * reduction b)
    (map_neg : ∀ a, reduction (-a) = -(reduction a))
    (x y r : R) (hr : reduction r * reduction r = -(1 : F))
    (hminus : reduction (x + -(r * y)) = 0) : reduction (x * x + y * y) = 0 := by
  have hminus' : reduction x + -(reduction r * reduction y) = 0 := by
    rw [map_add, map_neg, map_mul] at hminus
    exact hminus
  exact reduction_norm_zero_of_either_sign laws reduction map_add map_mul x y r hr
    (Or.inr hminus')

end ReductionMap
end JSP1012.ResidueNorm

#print axioms JSP1012.ResidueNorm.norm_zero_of_plus_sign
#print axioms JSP1012.ResidueNorm.norm_zero_of_minus_sign
#print axioms JSP1012.ResidueNorm.norm_zero_of_either_sign
#print axioms JSP1012.ResidueNorm.reduction_norm_zero_of_either_sign
#print axioms JSP1012.ResidueNorm.reduction_norm_zero_of_plus_kernel
#print axioms JSP1012.ResidueNorm.reduction_norm_zero_of_minus_kernel
