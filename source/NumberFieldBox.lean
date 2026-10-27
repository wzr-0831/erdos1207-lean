import NumberFieldCoordinates
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Ideal.Defs

/-!
# The actual finite box of algebraic integers

The selected set is defined by all actual real coordinates of a totally real
number field. Its finiteness is proved by embedding it injectively into the
Mathlib finite set of integral elements whose every complex conjugate is
bounded. No lattice-discreteness or box-finiteness assumption is introduced.

The closed box is finite for every real radius, including radius zero (and
negative radii). The ideal box is the actual filtered finset, with exact
membership statements. Cardinal upper bounds are proved separately.
-/

noncomputable section

namespace JSP1012.NumberFieldBox

open NumberField NumberFieldCoordinates

/-- Actual coordinate box of integral elements in a totally real number field. -/
def box (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] (X : ℝ) : Set (𝓞 K) :=
  {x | ∀ w : InfinitePlace K, realCoordinate x w ∈ Set.Icc (-X) X}

/-- Every complex embedding is controlled by the box, using its associated
infinite place and the actual real-coordinate absolute-value identity. -/
theorem conjugate_norm_le_of_mem_box {K : Type*} [Field K] [NumberField K]
    [IsTotallyReal K] {X : ℝ} {x : 𝓞 K} (hx : x ∈ box K X)
    (φ : K →+* ℂ) : ‖φ (x : K)‖ ≤ X := by
  have hxw := hx (InfinitePlace.mk φ)
  have habs : |realCoordinate x (InfinitePlace.mk φ)| ≤ X := abs_le.mpr hxw
  rw [abs_realCoordinate, InfinitePlace.apply] at habs
  exact habs

/-- The real coordinate box is genuinely finite, not merely postulated finite. -/
theorem box_finite (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (X : ℝ) : (box K X).Finite := by
  have hmap : Set.MapsTo (fun x : 𝓞 K => (x : K)) (box K X)
      {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ X} := by
    intro x hx
    exact ⟨RingOfIntegers.isIntegral_coe x, conjugate_norm_le_of_mem_box hx⟩
  have hinj : Set.InjOn (fun x : 𝓞 K => (x : K)) (box K X) := by
    intro x hx y hy hxy
    exact RingOfIntegers.coe_injective hxy
  exact Set.Finite.of_injOn hmap hinj (Embeddings.finite_of_norm_le K ℂ X)

/-- The finset contains exactly the elements of the proved finite coordinate box. -/
def boxFinset (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (X : ℝ) : Finset (𝓞 K) :=
  (box_finite K X).toFinset

@[simp] theorem mem_boxFinset {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (X : ℝ) (x : 𝓞 K) :
    x ∈ boxFinset K X ↔ ∀ w : InfinitePlace K, realCoordinate x w ∈ Set.Icc (-X) X := by
  exact (box_finite K X).mem_toFinset

theorem coe_boxFinset (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (X : ℝ) : (↑(boxFinset K X) : Set (𝓞 K)) = box K X :=
  (box_finite K X).coe_toFinset

/-- Intersection of the actual finite coordinate box with the given actual ideal. -/
def idealBoxFinset {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (I : Ideal (𝓞 K)) (X : ℝ) : Finset (𝓞 K) := by
  classical
  exact (boxFinset K X).filter (fun x => x ∈ I)

@[simp] theorem mem_idealBoxFinset {K : Type*} [Field K] [NumberField K]
    [IsTotallyReal K] (I : Ideal (𝓞 K)) (X : ℝ) (x : 𝓞 K) :
    x ∈ idealBoxFinset I X ↔
      x ∈ I ∧ ∀ w : InfinitePlace K, realCoordinate x w ∈ Set.Icc (-X) X := by
  classical
  simp only [idealBoxFinset, Finset.mem_filter, mem_boxFinset, and_comm]

/-- For nonnegative radius, the actual box is nonempty, since it contains zero. -/
theorem zero_mem_boxFinset {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    {X : ℝ} (hX : 0 ≤ X) : (0 : 𝓞 K) ∈ boxFinset K X := by
  rw [mem_boxFinset]
  intro w
  simp only [realCoordinate, map_zero, Set.mem_Icc]
  exact ⟨neg_nonpos.mpr hX, hX⟩

/-- Every ideal also contains the zero element of any nonnegative-radius box. -/
theorem zero_mem_idealBoxFinset {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (I : Ideal (𝓞 K)) {X : ℝ} (hX : 0 ≤ X) : (0 : 𝓞 K) ∈ idealBoxFinset I X := by
  rw [mem_idealBoxFinset]
  exact ⟨I.zero_mem, (mem_boxFinset X 0).mp (zero_mem_boxFinset hX)⟩

end JSP1012.NumberFieldBox

#print axioms JSP1012.NumberFieldBox.conjugate_norm_le_of_mem_box
#print axioms JSP1012.NumberFieldBox.box_finite
#print axioms JSP1012.NumberFieldBox.mem_boxFinset
#print axioms JSP1012.NumberFieldBox.mem_idealBoxFinset
#print axioms JSP1012.NumberFieldBox.zero_mem_idealBoxFinset
