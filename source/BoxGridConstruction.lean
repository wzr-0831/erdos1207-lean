import LowerCountBridgeCandidate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Actual finite Minkowski grids in the Euclidean plane

Source preparation, not a whole EP1207 theorem. The genuine discriminant
lower bound yields enough pairs of integral box elements; a subset has EXACT
prescribed cardinality. The planar map lands in EuclideanSpace, never the
sup-metric product of two real lines. Each selected real embedding is injective.

The radius/discriminant inequalities are explicit intermediate hypotheses;
their construction from the tower and integer radius is a separate obligation.
-/

noncomputable section

namespace JSP1012.BoxGridConstruction

open NumberField NumberFieldCoordinates NumberFieldBox

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- Squaring the actual lower lattice count gives enough pairs. -/
theorem card_square_ge (X : ℝ) (hX : 0 ≤ X) (D n : ℕ) (hD : 0 < D)
    (hdisc : |(NumberField.discr K : ℝ)| ≤ (D : ℝ) ^ Module.finrank ℚ K)
    (hradius : (D : ℝ) ^ Module.finrank ℚ K * n ≤
      X ^ (2 * Module.finrank ℚ K)) :
    n ≤ (boxFinset K X).card ^ 2 := by
  have hdisc0 : (NumberField.discr K : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero K
  have hsqrt : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 hdisc0)
  have hlo := (div_le_iff₀ hsqrt).mp (boxFinset_card_ge_discriminant K X hX)
  have hsq := pow_le_pow_left₀ (pow_nonneg hX (Module.finrank ℚ K)) hlo 2
  have hmain : (D : ℝ) ^ Module.finrank ℚ K * n ≤
      (D : ℝ) ^ Module.finrank ℚ K * ((boxFinset K X).card : ℝ) ^ 2 := by
    calc
      _ ≤ X ^ (2 * Module.finrank ℚ K) := hradius
      _ = (X ^ Module.finrank ℚ K) ^ 2 := by rw [← pow_mul]; congr 1; omega
      _ ≤ (((boxFinset K X).card : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|) ^ 2 := hsq
      _ = ((boxFinset K X).card : ℝ) ^ 2 * |(NumberField.discr K : ℝ)| := by
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      _ ≤ ((boxFinset K X).card : ℝ) ^ 2 * (D : ℝ) ^ Module.finrank ℚ K :=
        mul_le_mul_of_nonneg_left hdisc (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hDpow : 0 < (D : ℝ) ^ Module.finrank ℚ K := pow_pos (by exact_mod_cast hD) _
  have hn : (n : ℝ) ≤ ((boxFinset K X).card : ℝ) ^ 2 :=
    (mul_le_mul_iff_right₀ hDpow).mp hmain
  exact_mod_cast hn

/-- The selected grid consists of actual box pairs and has exactly n elements. -/
theorem exists_grid_card (X : ℝ) (hX : 0 ≤ X) (D n : ℕ) (hD : 0 < D)
    (hdisc : |(NumberField.discr K : ℝ)| ≤ (D : ℝ) ^ Module.finrank ℚ K)
    (hradius : (D : ℝ) ^ Module.finrank ℚ K * n ≤
      X ^ (2 * Module.finrank ℚ K)) :
    ∃ S : Finset (𝓞 K × 𝓞 K),
      S ⊆ (boxFinset K X) ×ˢ (boxFinset K X) ∧ S.card = n := by
  classical
  apply Finset.exists_subset_card_eq
  simpa only [Finset.card_product, pow_two] using card_square_ge X hX D n hD hdisc hradius

/-- A genuine Euclidean point, using the selected actual real embedding. -/
def planarPoint (w : InfinitePlace K) (z : 𝓞 K × 𝓞 K) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![realCoordinate z.1 w, realCoordinate z.2 w]

theorem planarPoint_injective (w : InfinitePlace K) : Function.Injective (planarPoint w) := by
  intro x y h
  have hx : realCoordinate x.1 w = realCoordinate y.1 w := congrArg (fun v => v 0) h
  have hy : realCoordinate x.2 w = realCoordinate y.2 w := congrArg (fun v => v 1) h
  have hinj : Function.Injective (fun z : 𝓞 K => realCoordinate z w) := by
    intro a b hab
    exact RingOfIntegers.coe_injective
      ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)).injective hab)
  exact Prod.ext (hinj hx) (hinj hy)

/-- Actual Euclidean distance squared is the chosen real embedding of the
integral sum of two squares. This also fixes the geometric distance notion. -/
theorem dist_sq_planarPoint (w : InfinitePlace K) (x y : 𝓞 K × 𝓞 K) :
    dist (planarPoint w x) (planarPoint w y) ^ 2 =
      realCoordinate ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) w := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, planarPoint, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.dist_eq, sq_abs,
    realCoordinate, map_add, map_pow, map_sub]

/-- Equality of integral squared-distance labels implies equality of genuine
nonnegative Euclidean distances; no default-label collision is admitted. -/
theorem dist_eq_of_sqLabel_eq (w : InfinitePlace K) (x y z : 𝓞 K × 𝓞 K)
    (h : (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 =
      (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2) :
    dist (planarPoint w x) (planarPoint w y) =
      dist (planarPoint w x) (planarPoint w z) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [dist_sq_planarPoint, dist_sq_planarPoint, h]

/-- Totally real number fields genuinely supply a place to use in the map. -/
theorem exists_planar_injection :
    ∃ f : (𝓞 K × 𝓞 K) → EuclideanSpace ℝ (Fin 2), Function.Injective f := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact ⟨planarPoint w, planarPoint_injective w⟩

/-- An actual prescribed-size planar set, together with its integral grid
preimage and the same real embedding used for all its distances. -/
theorem exists_planar_grid (X : ℝ) (hX : 0 ≤ X) (D n : ℕ) (hD : 0 < D)
    (hdisc : |(NumberField.discr K : ℝ)| ≤ (D : ℝ) ^ Module.finrank ℚ K)
    (hradius : (D : ℝ) ^ Module.finrank ℚ K * n ≤
      X ^ (2 * Module.finrank ℚ K)) :
    ∃ (w : InfinitePlace K) (S : Finset (𝓞 K × 𝓞 K))
      (P : Finset (EuclideanSpace ℝ (Fin 2))),
      S ⊆ (boxFinset K X) ×ˢ (boxFinset K X) ∧ S.card = n ∧
      P = S.image (planarPoint w) ∧ P.card = n := by
  classical
  obtain ⟨S, hS, hcard⟩ := exists_grid_card X hX D n hD hdisc hradius
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  refine ⟨w, S, S.image (planarPoint w), hS, hcard, rfl, ?_⟩
  rw [Finset.card_image_of_injective _ (planarPoint_injective w), hcard]

end JSP1012.BoxGridConstruction

#print axioms JSP1012.BoxGridConstruction.card_square_ge
#print axioms JSP1012.BoxGridConstruction.exists_grid_card
#print axioms JSP1012.BoxGridConstruction.planarPoint_injective
#print axioms JSP1012.BoxGridConstruction.dist_sq_planarPoint
#print axioms JSP1012.BoxGridConstruction.dist_eq_of_sqLabel_eq
#print axioms JSP1012.BoxGridConstruction.exists_planar_injection
#print axioms JSP1012.BoxGridConstruction.exists_planar_grid
