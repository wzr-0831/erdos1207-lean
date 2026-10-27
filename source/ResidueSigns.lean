import Std

/-!
# Abstract odd-characteristic residue-domain sign logic

The law interface below is universally quantified data, not a new global axiom
and not an assertion that a particular number field or residue field exists.
It lists only the elementary ring/domain laws actually used. Every field of
characteristic different from two supplies them, but that instantiation remains
an explicit obligation for a future number-field application.

The last theorem produces a finite sum-of-products certificate for the square
of a kernel. Its interpretation as membership in a Mathlib ideal product is
not silently asserted here.
-/

namespace JSP1012.ResidueSigns

universe u v

/-- The elementary residue-domain laws needed for the two-sign implication. -/
structure Laws (F : Type u) [Add F] [Mul F] [Neg F] [Zero F] [One F] : Prop where
  add_assoc : ∀ a b c : F, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : F, a + b = b + a
  zero_add : ∀ a : F, 0 + a = a
  add_zero : ∀ a : F, a + 0 = a
  add_neg_cancel : ∀ a : F, a + -a = 0
  add_mul : ∀ a b c : F, (a + b) * c = a * c + b * c
  one_mul : ∀ a : F, 1 * a = a
  zero_mul : ∀ a : F, 0 * a = 0
  no_zero_divisors : ∀ a b : F, a * b = 0 → a = 0 ∨ b = 0
  one_ne_zero : (1 : F) ≠ 0
  two_ne_zero : (1 : F) + 1 ≠ 0

section Residue
variable {F : Type u} [Add F] [Mul F] [Neg F] [Zero F] [One F]
variable (laws : Laws F)
include laws

/-- No nonzero element can be killed by doubling in odd characteristic. -/
theorem eq_zero_of_double_eq_zero (a : F) (h : a + a = 0) : a = 0 := by
  have hm : ((1 : F) + 1) * a = 0 := by
    rw [laws.add_mul, laws.one_mul, h]
  rcases laws.no_zero_divisors _ _ hm with ht | ha
  · exact False.elim (laws.two_ne_zero ht)
  · exact ha

theorem root_neg_one_ne_zero (r : F) (hr : r * r = -(1 : F)) : r ≠ 0 := by
  have hneg : -(1 : F) ≠ 0 := by
    intro hn
    have hc := laws.add_neg_cancel (1 : F)
    rw [hn, laws.add_zero] at hc
    exact laws.one_ne_zero hc
  intro hz
  rw [hz, laws.zero_mul] at hr
  exact hneg hr.symm

/-- If both residue signs hold, both coordinates vanish. No orderedness,
positivity, cardinality, or hidden characteristic-zero hypothesis is used. -/
theorem coordinates_eq_zero_of_both_signs (x y r : F)
    (hr : r * r = -(1 : F))
    (hplus : x + r * y = 0) (hminus : x + -(r * y) = 0) :
    x = 0 ∧ y = 0 := by
  have hxy : x = r * y := by
    calc
      x = (x + -(r * y)) + r * y := by
        rw [laws.add_assoc, laws.add_comm (-(r * y)) (r * y),
          laws.add_neg_cancel, laws.add_zero]
      _ = 0 + r * y := congrArg (fun z => z + r * y) hminus
      _ = r * y := laws.zero_add _
  have hdouble : r * y + r * y = 0 := by
    simpa only [hxy] using hplus
  have hry : r * y = 0 := eq_zero_of_double_eq_zero laws _ hdouble
  have hx : x = 0 := hxy.trans hry
  have hy : y = 0 := by
    rcases laws.no_zero_divisors r y hry with hr0 | hy0
    · exact False.elim (root_neg_one_ne_zero laws r hr hr0)
    · exact hy0
  exact ⟨hx, hy⟩

end Residue

section KernelSquare
variable {R : Type v} [Add R] [Mul R]

/-- Finite sums of products of members of `I`; each constructor is an explicit
certificate that belongs to an ideal square once `I` is instantiated as an ideal. -/
inductive SquareSpan (I : R → Prop) : R → Prop where
  | product (a b : R) : I a → I b → SquareSpan I (a * b)
  | add (a b : R) : SquareSpan I a → SquareSpan I b → SquareSpan I (a + b)

theorem norm_in_squareSpan {I : R → Prop} {x y : R} (hx : I x) (hy : I y) :
    SquareSpan I (x * x + y * y) :=
  SquareSpan.add _ _ (SquareSpan.product x x hx hx) (SquareSpan.product y y hy hy)

/-- The actual two-sign-to-square certificate, with the reduction map and its
residue laws explicit. No number-field ideal or quotient is postulated to exist. -/
theorem kernel_square_of_both_residue_signs
    {F : Type u} [Add F] [Mul F] [Neg F] [Zero F] [One F]
    (laws : Laws F) (reduction : R → F) (x y r : R)
    (hr : reduction r * reduction r = -(1 : F))
    (hplus : reduction x + reduction r * reduction y = 0)
    (hminus : reduction x + -(reduction r * reduction y) = 0) :
    SquareSpan (fun a => reduction a = 0) (x * x + y * y) := by
  obtain ⟨hx, hy⟩ := coordinates_eq_zero_of_both_signs laws _ _ _ hr hplus hminus
  exact norm_in_squareSpan hx hy

end KernelSquare
end JSP1012.ResidueSigns

#print axioms JSP1012.ResidueSigns.eq_zero_of_double_eq_zero
#print axioms JSP1012.ResidueSigns.coordinates_eq_zero_of_both_signs
#print axioms JSP1012.ResidueSigns.norm_in_squareSpan
#print axioms JSP1012.ResidueSigns.kernel_square_of_both_residue_signs
