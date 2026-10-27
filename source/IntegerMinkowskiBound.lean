import MinkowskiFiniteFree
import IntegerMass
import RealExponentFinish
import Mathlib.Tactic.Ring

/-!
# Exact integer cancellation and strict polynomial bound for actual free subsets

Source preparation. The large-subset mass inequality is the ACTUAL proved
Minkowski finite theorem. The small-subset branch is retained separately.
Only the explicit amplification, integer radius and degree-bracket arithmetic
conditions remain; they are supplied by separate parameter constructions.
-/

noncomputable section

namespace JSP1012.IntegerMinkowskiBound

open NumberField NumberFieldBox BoxGridConstruction MinkowskiResidueFamily
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

def augmentedProduct (f : SplitFamily K) : ℕ := (f.ps.map (fun p => p + 1)).prod

theorem augmentedProduct_pos (f : SplitFamily K) : 0 < augmentedProduct f := by
  apply List.prod_pos
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  omega

/-- The exact integer size bound for the large-subset branch. -/
theorem free_set_integer_bound (f : SplitFamily K) (w : InfinitePlace K)
    (A : Finset (𝓞 K × 𝓞 K)) (D m n : ℕ) (hD : 0 < D) (hm : 1 ≤ m)
    (hd : 0 < Module.finrank ℚ K)
    (hA : A ⊆ (boxFinset K ((Q f * m : ℕ) : ℝ)) ×ˢ
      (boxFinset K ((Q f * m : ℕ) : ℝ)))
    (hlarge : 2 * Q f ^ Module.finrank ℚ K ≤ A.card)
    (hfree : SetIsoscelesBridge.NoIsosceles
      (↑(A.image (planarPoint w)) : Set (EuclideanSpace ℝ (Fin 2))))
    (hamp : (16 * D) * (17 * augmentedProduct f) ≤ 2 ^ f.ps.length * Q f)
    (hradius : (Q f * m) ^ (2 * Module.finrank ℚ K) ≤
      (4 * D) ^ Module.finrank ℚ K * n) :
    2 ^ Module.finrank ℚ K * A.card ≤ n := by
  have hmass := MinkowskiFiniteFree.free_set_scaled_mass f w A m hm hd hA hlarge hfree
  exact IntegerMass.mass_cancellation (17 * augmentedProduct f) (2 ^ f.ps.length)
    (Q f) D m (Module.finrank ℚ K) A.card n
    (Nat.mul_pos (by decide) (augmentedProduct_pos f)) hD (Q_pos f) hd
    hamp hmass hradius

/-- Every actual isosceles-free subset is polynomially small. BOTH size
branches are proved; no large-subset assumption survives this endpoint. -/
theorem free_set_card_lt_rpow (f : SplitFamily K) (w : InfinitePlace K)
    (A : Finset (𝓞 K × 𝓞 K)) (D m n : ℕ) (hD : 0 < D) (hm : 1 ≤ m)
    (hd : 0 < Module.finrank ℚ K) (hn : 1 < n)
    (hA : A ⊆ (boxFinset K ((Q f * m : ℕ) : ℝ)) ×ˢ
      (boxFinset K ((Q f * m : ℕ) : ℝ)))
    (hfree : SetIsoscelesBridge.NoIsosceles
      (↑(A.image (planarPoint w)) : Set (EuclideanSpace ℝ (Fin 2))))
    (hamp : (16 * D) * (17 * augmentedProduct f) ≤ 2 ^ f.ps.length * Q f)
    (hradius : (Q f * m) ^ (2 * Module.finrank ℚ K) ≤
      (4 * D) ^ Module.finrank ℚ K * n)
    (hlo : ((10 * Q f) ^ 2) ^ Module.finrank ℚ K ≤ n)
    (hhi : n < ((10 * Q f) ^ 2) ^ (2 * Module.finrank ℚ K)) :
    (A.card : ℝ) < (n : ℝ) ^
      (1 - 1 / (4 * (((10 * Q f) ^ 2 : ℕ) : ℝ))) := by
  apply RealExponentFinish.card_lt_explicit_rpow (Q f) (Module.finrank ℚ K) n A.card
    (Q_pos f) hd hn hlo hhi
  by_cases hlarge : 2 * Q f ^ Module.finrank ℚ K ≤ A.card
  · exact Or.inr (free_set_integer_bound f w A D m n hD hm hd hA hlarge hfree hamp hradius)
  · exact Or.inl (Nat.lt_of_not_ge hlarge)

end JSP1012.IntegerMinkowskiBound

#print axioms JSP1012.IntegerMinkowskiBound.free_set_integer_bound
#print axioms JSP1012.IntegerMinkowskiBound.free_set_card_lt_rpow
