/-
The definition P below is adapted by definitional expansion from
FormalConjectures/ErdosProblems/1207.lean.
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The supremum-attainment and finite-image adapter proofs are independent.
-/

import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import SetIsoscelesBridge

/-!
# Exact FC1207 infimum/supremum bound from a finite bad set

STATUS: SOURCE-ONLY PREPARATION. This file has not been compiled.

`P` is a namespace-local, definitionally identical expansion of the frozen
`Erdos1207.P`; it is NOT a new or weakened extremal invariant. Its point space
is the genuine Euclidean space, its inner and outer extrema are in `Nat`, and
its free predicate is the exact expanded FC `Set.IsIsoscelesFree` predicate.
No noncollinearity hypothesis is present. The original FC module is not
imported into this partial integration, so no theorem below claims that an
actual FC import has already been kernel checked.

Frozen source: the Formal Conjectures repository; see THIRD_PARTY.md for excerpt provenance.
SHA256 of `FormalConjectures/ErdosProblems/1207.lean`:
`8909f676538fb4a1f21a219b274db83c36ce3be0aa8521a4f468da67291e8c97`.
The exact semantic expansion is in `SetIsoscelesBridge.NoIsosceles`.

For a supplied `n`-point set, its spectrum of free-subset cardinalities is
nonempty because the empty subset is free, and bounded above by the ambient
cardinality. Its natural-number supremum is therefore attained. This is what
preserves the STRICT real bound; a bare supremum inequality would not suffice.
The ambient set witnesses membership in the outer infimum family. No extra
positivity assumption on `n` or the real threshold is needed.
-/

noncomputable section

namespace JSP1012.FCBoundAdapter

open SetIsoscelesBridge
open scoped Classical

/-- The inner cardinality spectrum, retaining exactly the FC predicate. -/
def freeCardSpectrum {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Set ℕ :=
  {k : ℕ | ∃ A ⊆ S, NoIsosceles (A : Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}

/-- Exact expansion of the frozen FC1207 definition, in a private namespace. -/
def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S,
      NoIsosceles (A : Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}}

/-- The empty subset guarantees nonemptiness even when `S` itself is empty. -/
theorem zero_mem_freeCardSpectrum {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) : 0 ∈ freeCardSpectrum S := by
  refine ⟨∅, Finset.empty_subset S, ?_, Finset.card_empty⟩
  intro x hx
  exact (Finset.notMem_empty x hx).elim

theorem freeCardSpectrum_nonempty {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) : (freeCardSpectrum S).Nonempty :=
  ⟨0, zero_mem_freeCardSpectrum S⟩

/-- Every value is the cardinality of a genuine subset, hence at most `S.card`. -/
theorem freeCardSpectrum_bddAbove {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) : BddAbove (freeCardSpectrum S) := by
  refine ⟨S.card, ?_⟩
  rintro k ⟨A, hAS, _hfree, hcard⟩
  rw [← hcard]
  exact Finset.card_le_card hAS

/-- In particular, the spectrum is finite, not an uncontrolled real supremum. -/
theorem freeCardSpectrum_finite {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) : (freeCardSpectrum S).Finite :=
  Set.finite_iff_bddAbove.mpr (freeCardSpectrum_bddAbove S)

/-- The exact natural-number supremum is the cardinality of a free subset. -/
theorem freeCardSpectrum_sSup_attained {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) :
    ∃ A ⊆ S, NoIsosceles (A : Set (EuclideanSpace ℝ (Fin d))) ∧
      A.card = sSup (freeCardSpectrum S) :=
  Nat.sSup_mem (freeCardSpectrum_nonempty S) (freeCardSpectrum_bddAbove S)

/-- The supplied set witnesses a member of the actual outer infimum family. -/
theorem sSup_mem_outerFamily {d n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hcard : S.card = n) :
    sSup (freeCardSpectrum S) ∈
      {m : ℕ | ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card = n ∧
        m = sSup (freeCardSpectrum T)} :=
  ⟨S, hcard, rfl⟩

/-- All outer values are natural numbers, so zero is an explicit lower bound. -/
theorem outerFamily_bddBelow (d n : ℕ) :
    BddBelow {m : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
      m = sSup (freeCardSpectrum S)} :=
  ⟨0, fun m _ => Nat.zero_le m⟩

/-- No assumption about an extremum is postulated: this is the defining
infimum inequality, proved from the supplied set itself. -/
theorem P_le_sSup_freeCardSpectrum {d n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hcard : S.card = n) :
    P d n ≤ sSup (freeCardSpectrum S) := by
  change sInf {m : ℕ | ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card = n ∧
    m = sSup (freeCardSpectrum T)} ≤ sSup (freeCardSpectrum S)
  exact csInf_le (outerFamily_bddBelow d n) (sSup_mem_outerFamily S hcard)

/-- Every exact-FC-free subset strictly below `R` forces the same strict bound
on the guaranteed size. This includes all empty and small-input cases. -/
theorem P_lt_of_forall_subsets {d n : ℕ} {R : ℝ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hcard : S.card = n)
    (hbound : ∀ A ⊆ S, NoIsosceles (A : Set (EuclideanSpace ℝ (Fin d))) →
      (A.card : ℝ) < R) :
    (P d n : ℝ) < R := by
  obtain ⟨A, hAS, hfree, hA⟩ := freeCardSpectrum_sSup_attained S
  have hmax : ((sSup (freeCardSpectrum S) : ℕ) : ℝ) < R := by
    rw [← hA]
    exact hbound A hAS hfree
  exact lt_of_le_of_lt (Nat.cast_le.mpr (P_le_sSup_freeCardSpectrum S hcard)) hmax

/-- The same theorem without a local name for `P`, ready for definitional
conversion after importing the actual frozen FC module. -/
theorem fc_sInf_sSup_lt_of_forall_subsets {d n : ℕ} {R : ℝ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hcard : S.card = n)
    (hbound : ∀ A ⊆ S, NoIsosceles (A : Set (EuclideanSpace ℝ (Fin d))) →
      (A.card : ℝ) < R) :
    ((sInf {m : ℕ | ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card = n ∧
      m = sSup {k : ℕ | ∃ A ⊆ T,
        NoIsosceles (A : Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}} : ℕ) : ℝ) < R :=
  P_lt_of_forall_subsets S hcard hbound

/-- Any subset of a finite image has a finite preimage subset with the same
cardinality if the map is injective ON the original finite set. -/
theorem exists_subset_image_eq_card_of_injOn {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (hf : Set.InjOn f (S : Set α))
    (B : Finset β) (hB : B ⊆ S.image f) :
    ∃ A : Finset α, A ⊆ S ∧ A.image f = B ∧ A.card = B.card := by
  classical
  obtain ⟨A, hAS, hAB⟩ := Finset.subset_image_iff.mp hB
  refine ⟨A, hAS, hAB, ?_⟩
  have hAf : Set.InjOn f (A : Set α) :=
    fun _ hx _ hy hxy => hf (hAS hx) (hAS hy) hxy
  calc
    A.card = (A.image f).card := (Finset.card_image_of_injOn hAf).symm
    _ = B.card := congrArg Finset.card hAB

/-- Directly usable for the integral-grid construction: quantify subsets of
the source grid, but retain exact freeness of their actual Euclidean images. -/
theorem P_lt_of_image_subsets_bound {α : Type*} {d n : ℕ} {R : ℝ}
    (S : Finset α) (f : α → EuclideanSpace ℝ (Fin d))
    (hf : Set.InjOn f (S : Set α)) (hcard : S.card = n)
    (hbound : ∀ A ⊆ S,
      NoIsosceles (↑(A.image f) : Set (EuclideanSpace ℝ (Fin d))) →
      (A.card : ℝ) < R) :
    (P d n : ℝ) < R := by
  classical
  apply P_lt_of_forall_subsets (S.image f)
  · exact (Finset.card_image_of_injOn hf).trans hcard
  · intro B hB hfree
    obtain ⟨A, hAS, hAB, hcardAB⟩ :=
      exists_subset_image_eq_card_of_injOn S f hf B hB
    have hfreeA : NoIsosceles (↑(A.image f) : Set (EuclideanSpace ℝ (Fin d))) := by
      simpa only [hAB] using hfree
    simpa only [hcardAB] using hbound A hAS hfreeA

end JSP1012.FCBoundAdapter

#print axioms JSP1012.FCBoundAdapter.freeCardSpectrum_sSup_attained
#print axioms JSP1012.FCBoundAdapter.P_le_sSup_freeCardSpectrum
#print axioms JSP1012.FCBoundAdapter.P_lt_of_forall_subsets
#print axioms JSP1012.FCBoundAdapter.fc_sInf_sSup_lt_of_forall_subsets
#print axioms JSP1012.FCBoundAdapter.exists_subset_image_eq_card_of_injOn
#print axioms JSP1012.FCBoundAdapter.P_lt_of_image_subsets_bound
