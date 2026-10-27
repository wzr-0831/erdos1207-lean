import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Actual real coordinates and the integer algebraic norm

For an actual totally real number field, every infinite place is represented
by a real ring embedding and has multiplicity one. The infinite-place product
formula, together with the proved integer-to-rational norm compatibility, gives
the exact product of absolute coordinate values and of coordinate differences.

The norm identities below are PROVED from Mathlib theorems, not supplied as
hypotheses. No ideal norm lower bound, lattice estimate, number-field tower,
or geometric construction is asserted in this module.
-/

noncomputable section

namespace JSP1012.NumberFieldCoordinates

open NumberField
open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- The actual real embedding attached to each infinite place of a totally real field. -/
def realCoordinate (x : 𝓞 K) (w : InfinitePlace K) : ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) (x : K)

omit [NumberField K] in
/-- Its absolute value is precisely the original infinite-place value. -/
theorem abs_realCoordinate (z : 𝓞 K) (w : InfinitePlace K) :
    |realCoordinate z w| = w (z : K) := by
  simpa only [realCoordinate, Real.norm_eq_abs] using
    InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) (z : K)

/-- Coordinates genuinely respect subtraction, via their ring-embedding map law. -/
theorem realCoordinate_sub (x y : 𝓞 K) (w : InfinitePlace K) :
    realCoordinate (x - y) w = realCoordinate x w - realCoordinate y w := by
  exact map_sub (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    (x : K) (y : K)

/-- Actual product/norm identity for the full set of real coordinates. -/
theorem product_abs_realCoordinate (z : 𝓞 K) :
    (∏ w : InfinitePlace K, |realCoordinate z w|) =
      ((Algebra.norm ℤ z).natAbs : ℝ) := by
  calc
    (∏ w : InfinitePlace K, |realCoordinate z w|) =
        ∏ w : InfinitePlace K, w (z : K) := by
      apply Finset.prod_congr rfl
      intro w hw
      exact abs_realCoordinate z w
    _ = ∏ w : InfinitePlace K, w (z : K) ^ w.mult := by
      simp only [IsTotallyReal.mult_eq, pow_one]
    _ = ((|Algebra.norm ℚ (z : K)| : ℚ) : ℝ) :=
      InfinitePlace.prod_eq_abs_norm (z : K)
    _ = ((Algebra.norm ℤ z).natAbs : ℝ) := by
      rw [← Algebra.coe_norm_int, ← Int.cast_abs, Rat.cast_intCast, Nat.cast_natAbs]

/-- The exact difference product consumed by the ideal-norm packing theorem. -/
theorem product_abs_coordinate_difference (x y : 𝓞 K) :
    (∏ w : InfinitePlace K, |realCoordinate x w - realCoordinate y w|) =
      ((Algebra.norm ℤ (x - y)).natAbs : ℝ) := by
  rw [← product_abs_realCoordinate (x - y)]
  apply Finset.prod_congr rfl
  intro w hw
  rw [realCoordinate_sub]

end JSP1012.NumberFieldCoordinates

#print axioms JSP1012.NumberFieldCoordinates.realCoordinate_sub
#print axioms JSP1012.NumberFieldCoordinates.product_abs_realCoordinate
#print axioms JSP1012.NumberFieldCoordinates.product_abs_coordinate_difference
