import BoxGridConstruction
import Mathlib.Tactic.Linarith

/-!
# Actual integral squared distances of Minkowski-grid points

Source preparation. Every pair of actual box points has its integral sum of
two squared differences in the ACTUAL radius-8X² box. Distinct points give a
nonzero integral label because their genuine Euclidean images are distinct.
No product/sup metric is substituted for the Euclidean metric.
-/

noncomputable section

namespace JSP1012.SquaredDistanceBox

open NumberField NumberFieldCoordinates NumberFieldBox BoxGridConstruction

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

def squaredDifference (x y : 𝓞 K × 𝓞 K) : 𝓞 K :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

theorem realCoordinate_squaredDifference (w : InfinitePlace K) (x y : 𝓞 K × 𝓞 K) :
    realCoordinate (squaredDifference x y) w =
      (realCoordinate x.1 w - realCoordinate y.1 w) ^ 2 +
        (realCoordinate x.2 w - realCoordinate y.2 w) ^ 2 := by
  simp only [squaredDifference, realCoordinate, map_add, map_pow, map_sub]

/-- The exact constant eight comes from TWO coordinate differences of size
at most 2X each. Closed endpoints and X=0 are retained. -/
theorem squaredDifference_mem_box {X : ℝ} (hX : 0 ≤ X)
    {x y : 𝓞 K × 𝓞 K}
    (hx : x ∈ (boxFinset K X) ×ˢ (boxFinset K X))
    (hy : y ∈ (boxFinset K X) ×ˢ (boxFinset K X)) :
    squaredDifference x y ∈ boxFinset K (8 * X ^ 2) := by
  classical
  rw [mem_boxFinset]
  intro w
  have hx1 := (mem_boxFinset X x.1).mp (Finset.mem_product.mp hx).1 w
  have hx2 := (mem_boxFinset X x.2).mp (Finset.mem_product.mp hx).2 w
  have hy1 := (mem_boxFinset X y.1).mp (Finset.mem_product.mp hy).1 w
  have hy2 := (mem_boxFinset X y.2).mp (Finset.mem_product.mp hy).2 w
  have hdx : |realCoordinate x.1 w - realCoordinate y.1 w| ≤ 2 * X := by
    exact abs_le.mpr ⟨by linarith [hx1.1, hy1.2], by linarith [hx1.2, hy1.1]⟩
  have hdy : |realCoordinate x.2 w - realCoordinate y.2 w| ≤ 2 * X := by
    exact abs_le.mpr ⟨by linarith [hx2.1, hy2.2], by linarith [hx2.2, hy2.1]⟩
  have hdx2 : (realCoordinate x.1 w - realCoordinate y.1 w) ^ 2 ≤ (2 * X) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ 2 * X)).mpr hdx
  have hdy2 : (realCoordinate x.2 w - realCoordinate y.2 w) ^ 2 ≤ (2 * X) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ 2 * X)).mpr hdy
  rw [realCoordinate_squaredDifference]
  constructor
  · nlinarith [sq_nonneg (realCoordinate x.1 w - realCoordinate y.1 w),
      sq_nonneg (realCoordinate x.2 w - realCoordinate y.2 w)]
  · nlinarith [hdx2, hdy2]

theorem squaredDifference_coordinate_pos (w : InfinitePlace K) {x y : 𝓞 K × 𝓞 K}
    (hxy : x ≠ y) : 0 < realCoordinate (squaredDifference x y) w := by
  unfold squaredDifference
  rw [← dist_sq_planarPoint]
  exact pow_pos (dist_pos.mpr ((planarPoint_injective w).ne hxy)) 2

/-- A repeated integral label cannot be the artificial zero label for a
distinct pair: positivity is proved in the chosen genuine real embedding. -/
theorem squaredDifference_ne_zero (w : InfinitePlace K) {x y : 𝓞 K × 𝓞 K}
    (hxy : x ≠ y) : squaredDifference x y ≠ 0 := by
  intro hz
  have hpos := squaredDifference_coordinate_pos w hxy
  rw [hz] at hpos
  simpa [realCoordinate] using hpos

end JSP1012.SquaredDistanceBox

#print axioms JSP1012.SquaredDistanceBox.squaredDifference_mem_box
#print axioms JSP1012.SquaredDistanceBox.squaredDifference_coordinate_pos
#print axioms JSP1012.SquaredDistanceBox.squaredDifference_ne_zero
