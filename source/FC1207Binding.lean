/-
Copyright 2025-2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Only the five marked definition/notation excerpts below are copied from the
frozen Formal Conjectures source. The binding proofs are independently added.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FCBoundAdapter

/-!
# Frozen FC1207 definition-only binding — design-review source

NOT COMPILED. NOT AN IMPORT OF THE ORIGINAL FORMAL CONJECTURES MODULE.

This isolated module preserves the exact upstream declaration names and
definition bodies needed by `Erdos1207.P`. It does not impersonate an upstream
module path, import the upstream theorem placeholder, or alter frozen source.
The source hashes, exact excerpt checks, excluded import closure, and proposed
scope of any future kernel check are in `FC1207Binding-audit.md`.

The original FC umbrella targets Lean/Mathlib 4.33.1 and has an unavailable
dependency in both installed 4.35 environments. This source is therefore an
explicit, separately reviewable DEFINITION EXTRACTION, not a silent substitute
for an upstream build. It must not be imported together with the original FC
geometry/EP1207 modules: the preserved declaration names would collide.

`FrozenTarget` records the exact upstream proposition without asserting it.
The new theorems only bind those frozen definitions to the verified local
adapter. In particular none uses `Erdos1207.erdos_1207`, which is NOT declared
here. A successful future check would certify this extracted-definition gate,
not whole-problem completion or upstream project CI.
-/

-- BEGIN EXACT EXCERPT: Geometry/Euclidean.lean:22
scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
-- END EXACT EXCERPT

namespace Set

variable {α : Type*}

-- BEGIN EXACT EXCERPT: Data/Set/Triplewise.lean:36-37
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z
-- END EXACT EXCERPT

end Set

-- BEGIN EXACT EXCERPT: Geometry/2d.lean:262-263
def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q
-- END EXACT EXCERPT

-- BEGIN EXACT EXCERPT: Geometry/2d.lean:269-270
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z
-- END EXACT EXCERPT

open Filter
open scoped EuclideanGeometry

namespace Erdos1207

-- BEGIN EXACT EXCERPT: ErdosProblems/1207.lean:46-48
noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S, (A : Set (ℝ^d)).IsIsoscelesFree ∧ A.card = k}}
-- END EXACT EXCERPT

end Erdos1207

namespace JSP1012.FC1207Binding

/-- The exact original proposition, recorded as a proposition-valued definition;
this is not a proof of the proposition. Only the reference to `P` is qualified. -/
def FrozenTarget : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (Erdos1207.P 2 n : ℝ) < (n : ℝ) ^ (1 - c)

/-- All three cyclic side equalities and the original distinctness order are
retained. No noncollinearity or nondegeneracy condition has been added. -/
theorem isIsoscelesFree_iff_exact {α : Type*} [Dist α] (A : Set α) :
    A.IsIsoscelesFree ↔ SetIsoscelesBridge.NoIsosceles A :=
  Iff.rfl

/-- Point types, `Nat` extrema, and the free predicate coincide definitionally. -/
theorem P_eq_adapter (d n : ℕ) : Erdos1207.P d n = FCBoundAdapter.P d n :=
  rfl

/-- The entire statement type, including eventuality, real coercions and real
power, is the frozen EP1207 statement, not a weakened variant. -/
theorem frozenTarget_iff_adapter :
    FrozenTarget ↔
      ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        (FCBoundAdapter.P 2 n : ℝ) < (n : ℝ) ^ (1 - c) :=
  Iff.rfl

/-- Exact-n finite witnesses transfer to the preserved frozen `Erdos1207.P`.
The all-subsets hypothesis remains a genuine, explicit proof obligation. -/
theorem P_lt_of_forall_subsets {d n : ℕ} {R : ℝ}
    (S : Finset (ℝ^d)) (hcard : S.card = n)
    (hbound : ∀ A ⊆ S, (A : Set (ℝ^d)).IsIsoscelesFree → (A.card : ℝ) < R) :
    (Erdos1207.P d n : ℝ) < R := by
  rw [P_eq_adapter]
  apply FCBoundAdapter.P_lt_of_forall_subsets S hcard
  intro A hAS hfree
  exact hbound A hAS ((isIsoscelesFree_iff_exact (A : Set (ℝ^d))).mpr hfree)

end JSP1012.FC1207Binding

#print axioms JSP1012.FC1207Binding.isIsoscelesFree_iff_exact
#print axioms JSP1012.FC1207Binding.P_eq_adapter
#print axioms JSP1012.FC1207Binding.frozenTarget_iff_adapter
#print axioms JSP1012.FC1207Binding.P_lt_of_forall_subsets
