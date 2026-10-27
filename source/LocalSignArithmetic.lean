import LocalResidueCoordinates
import SignOverlap
import IdealSubsetWeights

/-!
# Actual local-sign arithmetic in the finite overlap argument

Source preparation. A compatible sign word forces the integral sum of two
squares into EVERY actual coordinate ideal; coprimality gives its membership
in their product. Both permitted signs are counted only when the SAME actual
ideal square contains that SAME integral label.
-/

noncomputable section

namespace JSP1012.LocalSignArithmetic

open LocalResidueCoordinates SignedResidueVectors
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Infinite R]

def ideals (cs : List (GoodCoordinate R)) : List (Ideal R) := cs.map (fun c => c.I)

def idealSet (cs : List (GoodCoordinate R)) : Finset (Ideal R) := by
  classical
  exact (ideals cs).toFinset

def baseCoordinates (cs : List (GoodCoordinate R)) : List (Coordinate R) :=
  cs.map GoodCoordinate.toCoordinate

def squareBits (cs : List (GoodCoordinate R)) (z : R) : List Bool := by
  classical
  exact cs.map (fun c => decide (z ∈ c.I ^ 2))

/-- The actual signs, with roots fixed in cs, force membership in each ideal. -/
theorem norm_mem_each_of_compatible (cs : List (GoodCoordinate R)) (word : List Bool)
    (hlen : word.length = cs.length) (x y : R)
    (hcompat : SignOverlap.compatible
      (signPermissions (baseCoordinates cs) x y) word = true) :
    ∀ c ∈ cs, x ^ 2 + y ^ 2 ∈ c.I := by
  induction cs generalizing word with
  | nil => simp
  | cons c cs ih =>
    cases word with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons sign word =>
      have htail : word.length = cs.length := Nat.succ.inj hlen
      have hparts :
          (if sign then (c.toCoordinate.permissions x y).2
            else (c.toCoordinate.permissions x y).1) = true ∧
          SignOverlap.compatible (signPermissions (baseCoordinates cs) x y) word = true := by
        simpa only [baseCoordinates, List.map_cons, signPermissions, SignOverlap.compatible,
          Bool.and_eq_true] using hcompat
      intro a ha
      rcases List.mem_cons.mp ha with hac | ha
      · rw [hac]
        exact norm_mem_of_permission c sign x y hparts.1
      · exact ih word htail hparts.2 a ha

/-- Actual coprime ideal intersection gives the full product membership.
The final coordinate construction supplies this coprimality by maximality. -/
theorem norm_mem_product_of_compatible (cs : List (GoodCoordinate R))
    (hcoprime : (idealSet cs : Set (Ideal R)).Pairwise IsCoprime)
    (word : List Bool) (hlen : word.length = cs.length) (x y : R)
    (hcompat : SignOverlap.compatible
      (signPermissions (baseCoordinates cs) x y) word = true) :
    x ^ 2 + y ^ 2 ∈ ∏ I ∈ idealSet cs, I := by
  classical
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcoprime]
  simp only [Submodule.mem_iInf]
  intro I hI
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hI)
  exact norm_mem_each_of_compatible cs word hlen x y hcompat c hc

/-- Every both-sign coordinate is included in the actual square-divisor bits.
Repeated equal numerical norms never collapse distinct ideal coordinates. -/
theorem bothCount_le_square_count (cs : List (GoodCoordinate R)) (x y : R) :
    SignOverlap.bothCount (signPermissions (baseCoordinates cs) x y) ≤
      (squareBits cs (x ^ 2 + y ^ 2)).countP id := by
  classical
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    have hhead :
        (if (c.toCoordinate.permissions x y).1 && (c.toCoordinate.permissions x y).2
          then 1 else 0) ≤ (if decide (x ^ 2 + y ^ 2 ∈ c.I ^ 2) then 1 else 0) := by
      cases hb : ((c.toCoordinate.permissions x y).1 && (c.toCoordinate.permissions x y).2) with
      | false => simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
      | true =>
        have hparts := Bool.and_eq_true_iff.mp hb
        have hmem := norm_mem_square_of_both_permissions c x y hparts.1 hparts.2
        simp only [hb, hmem, decide_true, ↓reduceIte, Nat.le_refl]
    simp only [baseCoordinates, List.map_cons, signPermissions, SignOverlap.bothCount,
      squareBits, List.map_cons, List.countP_cons, id_eq] at ih ⊢
    omega

end JSP1012.LocalSignArithmetic

#print axioms JSP1012.LocalSignArithmetic.norm_mem_each_of_compatible
#print axioms JSP1012.LocalSignArithmetic.norm_mem_product_of_compatible
#print axioms JSP1012.LocalSignArithmetic.bothCount_le_square_count
