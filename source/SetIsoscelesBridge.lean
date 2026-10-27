/-
The definition NoIsosceles below expands definitions adapted from
FormalConjecturesForMathlib/Data/Set/Triplewise.lean and
FormalConjecturesForMathlib/Geometry/2d.lean.
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The equivalence and pullback proofs are independently implemented here.
-/

import Mathlib.Topology.MetricSpace.Defs
import FinsetEnumeration
import BoxGridConstruction

/-!
# Exact set-level isosceles semantics and finite-index pullback

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.


NoIsosceles is EXACTLY the expanded Formal Conjectures definition:
Set.Triplewise (fun x y z => not IsIsosceles x y z), retaining its implicit
point binders and distinctness order x≠y, y≠z, x≠z. In particular all three
cyclic side-equality alternatives are forbidden. We neither import all of FC
nor declare potentially conflicting global Set.IsIsoscelesFree definitions.

The apex-free equivalence uses only distance symmetry and permutations. There
is NO noncollinearity, nondegenerate-triangle, or extra nonzero-side condition.
Thus equally spaced collinear triples are excluded, just as in FC1207 / LPZ26.
The actual planar/integer-index bridge uses a proved injective point map and
bounded finite enumeration, never global fallback injectivity.
-/

namespace JSP1012.SetIsoscelesBridge

open scoped Classical

/-- Exact expanded FC set-level triplewise predicate, in a private namespace. -/
def NoIsosceles {α : Type*} [Dist α] (A : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A →
    x ≠ y → y ≠ z → x ≠ z →
      ¬ (dist x y = dist y z ∨ dist y z = dist z x ∨ dist z x = dist x y)

/-- The generic apex condition, also usable for pulled-back true distances. -/
def ApexFreeFor {α D : Type*} (A : Set α) (distance : α → α → D) : Prop :=
  ∀ x, x ∈ A → ∀ y, y ∈ A → ∀ z, z ∈ A →
    x ≠ y → x ≠ z → y ≠ z → distance x y ≠ distance x z

/-- The exact FC condition is equivalent to the apex condition used by the
finite sieve; symmetry/permutations account for all three side equalities. -/
theorem noIsosceles_iff_apexFree {α : Type*} [MetricSpace α] (A : Set α) :
    NoIsosceles A ↔ ApexFreeFor A dist := by
  constructor
  · intro h x hx y hy z hz hxy hxz hyz heq
    exact h hx hy hz hxy hyz hxz
      (Or.inr (Or.inr ((dist_comm z x).trans heq.symm)))
  · intro h x hx y hy z hz hxy hyz hxz hsides
    rcases hsides with hxy_yz | hyz_zx | hzx_xy
    · exact h y hy x hx z hz hxy.symm hyz hxz ((dist_comm y x).trans hxy_yz)
    · exact h z hz y hy x hx hyz.symm hxz.symm hxy.symm ((dist_comm z y).trans hyz_zx)
    · exact h x hx y hy z hz hxy hxz hyz (hzx_xy.symm.trans (dist_comm z x))

/-- Finite-set specialization in the exact explicit apex form. -/
theorem finset_noIsosceles_iff {α : Type*} [MetricSpace α] (S : Finset α) :
    NoIsosceles (S : Set α) ↔
      ∀ x, x ∈ S → ∀ y, y ∈ S → ∀ z, z ∈ S →
        x ≠ y → x ≠ z → y ≠ z → dist x y ≠ dist x z :=
  noIsosceles_iff_apexFree (S : Set α)

/-- Monotonicity has exactly the original FC set semantics. -/
theorem noIsosceles_mono {α : Type*} [Dist α] {A B : Set α}
    (hBA : B ⊆ A) (hA : NoIsosceles A) : NoIsosceles B := by
  intro x hx y hy z hz hxy hyz hxz
  exact hA (hBA hx) (hBA hy) (hBA hz) hxy hyz hxz

/-- An injection ON the selected set is enough; the domain needs no metric.
The output distance is the actual target metric pulled back by the same map. -/
theorem apexFree_pullback_of_noIsosceles {α β : Type*} [MetricSpace β]
    (A : Set α) (f : α → β) (hinjective : Set.InjOn f A)
    (himage : NoIsosceles (f '' A)) :
    ApexFreeFor A (fun x y => dist (f x) (f y)) := by
  have hfree := (noIsosceles_iff_apexFree (f '' A)).mp himage
  intro x hx y hy z hz hxy hxz hyz
  apply hfree (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩ (f z) ⟨z, hz, rfl⟩
  · exact fun h => hxy (hinjective hx hy h)
  · exact fun h => hxz (hinjective hx hz h)
  · exact fun h => hyz (hinjective hy hz h)

/-- Finset-image form using an actual globally injective map. -/
theorem finset_apexFree_of_image_noIsosceles {α β : Type*} [MetricSpace β]
    (S : Finset α) (f : α → β) (hinjective : Function.Injective f)
    (himage : NoIsosceles (↑(S.image f) : Set β)) :
    ∀ x, x ∈ S → ∀ y, y ∈ S → ∀ z, z ∈ S →
      x ≠ y → x ≠ z → y ≠ z → dist (f x) (f y) ≠ dist (f x) (f z) := by
  have hset : NoIsosceles (f '' (S : Set α)) := by
    simpa only [Finset.coe_image] using himage
  exact apexFree_pullback_of_noIsosceles (S : Set α) f
    (fun _ _ _ _ h => hinjective h) hset

/-- The true-distance finite core receives exactly the free-set predicate
required by FC, through the actual bounded finite enumeration. -/
theorem indexed_free_of_image_noIsosceles {α β : Type*} [MetricSpace β]
    (S : Finset α) (fallback : α) (f : α → β) (hinjective : Function.Injective f)
    (himage : NoIsosceles (↑(S.image f) : Set β)) :
    IsoscelesFree S.card (fun _ => true)
      (fun i j => dist (f (FinsetEnumeration.pointAt S fallback i))
        (f (FinsetEnumeration.pointAt S fallback j))) := by
  apply FinsetEnumeration.indexed_free_of_free S fallback (fun x y => dist (f x) (f y))
  exact finset_apexFree_of_image_noIsosceles S f hinjective himage

section ActualPlanarMap

open NumberField BoxGridConstruction

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- Actual planar-grid instance, using the proved real-embedding injection.
No geometric interpretation of arbitrary natural labels is asserted here. -/
theorem indexed_planar_free_of_image_noIsosceles (w : InfinitePlace K)
    (S : Finset (𝓞 K × 𝓞 K)) (fallback : 𝓞 K × 𝓞 K)
    (himage : NoIsosceles (↑(S.image (planarPoint w)) : Set (EuclideanSpace ℝ (Fin 2)))) :
    IsoscelesFree S.card (fun _ => true)
      (fun i j => dist (planarPoint w (FinsetEnumeration.pointAt S fallback i))
        (planarPoint w (FinsetEnumeration.pointAt S fallback j))) := by
  apply indexed_free_of_image_noIsosceles S fallback (planarPoint w) (planarPoint_injective w)
  simpa only [Finset.coe_image] using himage

end ActualPlanarMap
end JSP1012.SetIsoscelesBridge

#print axioms JSP1012.SetIsoscelesBridge.noIsosceles_iff_apexFree
#print axioms JSP1012.SetIsoscelesBridge.finset_noIsosceles_iff
#print axioms JSP1012.SetIsoscelesBridge.apexFree_pullback_of_noIsosceles
#print axioms JSP1012.SetIsoscelesBridge.indexed_free_of_image_noIsosceles
#print axioms JSP1012.SetIsoscelesBridge.indexed_planar_free_of_image_noIsosceles
