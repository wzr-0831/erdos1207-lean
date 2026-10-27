import IntegerMinkowskiBound
import IntegerRadius
import FCBoundAdapter

/-!
# Actual prescribed-size planar construction and exact FC P bound

Source preparation. Starting from ONE actual totally real split field and
the explicit degree/radius/amplification inequalities, this constructs a
genuine n-point Euclidean grid and proves the exact expanded FC P bound.

This is still conditional on the displayed field/discriminant input. It is
not a whole EP1207 endpoint until the actual exact-degree tower and parameter
selection instantiate those conditions in one verified toolchain.
-/

noncomputable section

namespace JSP1012.FinitePolynomialConstruction

open NumberField NumberFieldBox BoxGridConstruction MinkowskiResidueFamily
open IntegerMinkowskiBound
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- An actual n-point construction, not merely an assumed finite certificate.
Every isosceles-free subset is treated, including the small-subset branch. -/
theorem P_lt_of_split_field (f : SplitFamily K) (D n : ℕ) (hD : 0 < D)
    (hd : 0 < Module.finrank ℚ K) (hn : 1 < n)
    (hdisc : |(NumberField.discr K : ℝ)| ≤ (D : ℝ) ^ Module.finrank ℚ K)
    (hamp : (16 * D) * (17 * augmentedProduct f) ≤ 2 ^ f.ps.length * Q f)
    (hlo : ((10 * Q f) ^ 2) ^ Module.finrank ℚ K ≤ n)
    (hhi : n < ((10 * Q f) ^ 2) ^ (2 * Module.finrank ℚ K)) :
    (FCBoundAdapter.P 2 n : ℝ) < (n : ℝ) ^
      (1 - 1 / (4 * (((10 * Q f) ^ 2 : ℕ) : ℝ))) := by
  classical
  obtain ⟨m, hm, hradiusLower, hradiusUpper⟩ :=
    IntegerRadius.exists_integer_radius_of_bracket (Q f) D (Module.finrank ℚ K) n
      (Q_pos f) hD hd hlo
  let X : ℝ := ((Q f * m : ℕ) : ℝ)
  have hX : 0 ≤ X := by positivity
  have hradiusReal : (D : ℝ) ^ Module.finrank ℚ K * n ≤
      X ^ (2 * Module.finrank ℚ K) := by
    dsimp only [X]
    exact_mod_cast hradiusLower
  obtain ⟨S, hS, hScard⟩ := exists_grid_card X hX D n hD hdisc hradiusReal
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  apply FCBoundAdapter.P_lt_of_image_subsets_bound S (planarPoint w)
    (fun _ _ _ _ h => (planarPoint_injective w) h) hScard
  intro A hAS hfree
  exact free_set_card_lt_rpow f w A D m n hD hm hd hn
    (hAS.trans hS) (by simpa only [Finset.coe_image] using hfree)
    hamp hradiusUpper hlo hhi

end JSP1012.FinitePolynomialConstruction

#print axioms JSP1012.FinitePolynomialConstruction.P_lt_of_split_field
