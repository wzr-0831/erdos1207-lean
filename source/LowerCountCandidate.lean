/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Source-only compatibility candidate: unconditional additive-box lower bound

Extracted without proof edits from mathlib-initiative/sum_product commit
80e4127a67742659d521466204c6d2d7e0ca2b3f (Apache-2.0; retained LICENSE).
Boxes.lean: 23-43. AdditiveCount.lean: 106-120, 219-268, 310-444.
Only unused declarations/imports have been removed; this file has NOT been compiled.
Upstream toolchain is 4.31.0-rc1. Candidate target is existing official Mathlib 4.35.
-/

open scoped NumberField
open Pointwise

namespace SumProduct

/-- The additive box `B⁺(X) = {α ∈ 𝒪_K : w(α) ≤ X for every infinite place w}`
(i.e. all archimedean absolute values of `α` are `≤ X`). -/
def boxAddSet (K : Type*) [Field K] [NumberField K] (X : ℝ) : Set (𝓞 K) :=
  {α | ∀ w : NumberField.InfinitePlace K, w (α : K) ≤ X}

theorem boxAddSet_finite (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    (boxAddSet K X).Finite := by
  refine Set.Finite.of_finite_image (f := fun α : 𝓞 K => (α : K)) ?_
    (fun a _ b _ hab => NumberField.RingOfIntegers.coe_injective hab)
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ X).subset ?_
  rintro x ⟨α, hα, rfl⟩
  exact ⟨NumberField.RingOfIntegers.isIntegral_coe α, fun φ => by
    rw [← NumberField.InfinitePlace.apply φ]; exact hα (NumberField.InfinitePlace.mk φ)⟩

/-- The additive box `B⁺(X)` as a `Finset`. -/
noncomputable def boxAdd (K : Type*) [Field K] [NumberField K] (X : ℝ) : Finset (𝓞 K) :=
  (boxAddSet_finite K X).toFinset

@[simp] theorem mem_boxAdd {K : Type*} [Field K] [NumberField K] {X : ℝ} {α : 𝓞 K} :
    α ∈ boxAdd K X ↔ ∀ w : NumberField.InfinitePlace K, w (α : K) ≤ X :=
  Set.Finite.mem_toFinset _

open scoped Classical in
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- Volume of the open box `{x : mixedSpace K | ∀ w, normAtPlace w x < r}` for a totally real
field of degree `d`: it is `(2r)^d`. This is the box used in the Blichfeldt lower bound. -/
theorem volume_convexBodyLT_const {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (r : NNReal) :
    volume (convexBodyLT K (fun _ => r)) = (2 : ENNReal) ^ d * (r : ENNReal) ^ d := by
  have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
  have hr : nrRealPlaces K = d := by
    have h := card_add_two_mul_card_eq_rank K
    rw [hd, h0] at h; omega
  have hsum : ∑ w : InfinitePlace K, mult w = d := by rw [sum_mult_eq, hd]
  rw [convexBodyLT_volume, convexBodyLTFactor, h0, pow_zero, mul_one, hr,
    Finset.prod_pow_eq_pow_sum, hsum, ENNReal.coe_pow]
  norm_num

open NumberField NumberField.mixedEmbedding in
/-- The additive embedding `𝒪_K ↪ mixedSpace K` (the mixed embedding restricted to the integers).
Its range is `mixedEmbedding.integerLattice K`. -/
noncomputable def latticeEmbed (K : Type*) [Field K] [NumberField K] : 𝓞 K →+ mixedSpace K :=
  ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toAddMonoidHom

@[simp] theorem latticeEmbed_apply {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    latticeEmbed K α = NumberField.mixedEmbedding K (algebraMap (𝓞 K) K α) := rfl

theorem latticeEmbed_injective {K : Type*} [Field K] [NumberField K] :
    Function.Injective (latticeEmbed K) :=
  (NumberField.mixedEmbedding_injective K).comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
theorem normAtPlace_latticeEmbed {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (w : InfinitePlace K) : normAtPlace w (latticeEmbed K α) = w (α : K) := by
  rw [latticeEmbed_apply, normAtPlace_apply]

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Metric in
/-- Membership in the open box `convexBodyLT K f`, in terms of `normAtPlace`. -/
theorem mem_convexBodyLT_iff {K : Type*} [Field K] [NumberField K] (f : InfinitePlace K → NNReal)
    (y : mixedSpace K) : y ∈ convexBodyLT K f ↔ ∀ w : InfinitePlace K, normAtPlace w y < f w := by
  simp only [convexBodyLT, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall]
  constructor
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw
  · intro h
    exact ⟨fun w hw => by rw [← normAtPlace_apply_of_isReal hw]; exact h w,
           fun w hw => by rw [← normAtPlace_apply_of_isComplex hw]; exact h w⟩

open NumberField NumberField.mixedEmbedding in
/-- The range of `latticeEmbed` is exactly the integer lattice. -/
theorem range_latticeEmbed (K : Type*) [Field K] [NumberField K] :
    Set.range (latticeEmbed K) = ↑(mixedEmbedding.integerLattice K) := by
  rw [mixedEmbedding.integerLattice, LinearMap.coe_range]
  rfl

open NumberField NumberField.mixedEmbedding in
/-- The bijection `𝒪_K ≃ integerLattice K` induced by the (injective) lattice embedding. -/
noncomputable def latticeEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ ↥(mixedEmbedding.integerLattice K) :=
  (Equiv.ofInjective (latticeEmbed K) latticeEmbed_injective).trans
    (Set.equivOfEq (range_latticeEmbed K))

open NumberField.mixedEmbedding in
@[simp] theorem latticeEquiv_coe {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    ((latticeEquiv K α : mixedSpace K)) = latticeEmbed K α := rfl

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- `encard` form of `count_le_boxAdd` (the form needed for the tsum bound). -/
theorem count_encard_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.encard
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ℕ∞) := by
  set T := {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} with hT
  rcases T.eq_empty_or_nonempty with he | ⟨α₀, hα₀⟩
  · simp [he]
  · have hinj : Set.InjOn (· - α₀) T := fun a _ b _ h => by linear_combination h
    have hsub : (· - α₀) '' T ⊆ ↑(boxAdd K (2 * (r : ℝ))) := by
      rintro _ ⟨α, hα, rfl⟩
      have hαmem : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r) := hα
      have hα₀mem : latticeEmbed K α₀ + x ∈ convexBodyLT K (fun _ => r) := hα₀
      rw [Finset.mem_coe, mem_boxAdd]
      intro w
      rw [← normAtPlace_latticeEmbed]
      have e : latticeEmbed K (α - α₀)
          = (latticeEmbed K α + x) - (latticeEmbed K α₀ + x) := by rw [map_sub]; abel
      rw [e]
      have key : normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
          ≤ normAtPlace w (latticeEmbed K α + x) + normAtPlace w (latticeEmbed K α₀ + x) := by
        calc normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
            = normAtPlace w ((latticeEmbed K α + x) + -(latticeEmbed K α₀ + x)) := by
              rw [sub_eq_add_neg]
          _ ≤ normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (-(latticeEmbed K α₀ + x)) := normAtPlace_add_le w _ _
          _ = normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (latticeEmbed K α₀ + x) := by rw [normAtPlace_neg]
      have h1 := (mem_convexBodyLT_iff _ _).mp hαmem w
      have h2 := (mem_convexBodyLT_iff _ _).mp hα₀mem w
      have : (2 : ℝ) * (r : ℝ) = (r : ℝ) + (r : ℝ) := by ring
      linarith
    calc T.encard = ((· - α₀) '' T).encard := (Set.InjOn.encard_image hinj).symm
      _ ≤ (↑(boxAdd K (2 * (r : ℝ))) : Set (𝓞 K)).encard := Set.encard_le_encard hsub
      _ = ((boxAdd K (2 * (r : ℝ))).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- The multiplicity at `x`: the number of lattice points `ℓ` with `ℓ + x` in the radius-`r` box
is at most `|B⁺(2r)|`. (Tsum form of `count_encard_le`, reindexed over `𝒪_K`.) -/
theorem tsum_indicator_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    ∑' l : ↥(mixedEmbedding.integerLattice K),
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) ((l : mixedSpace K) + x)
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ENNReal) := by
  have hfun : (fun α : 𝓞 K =>
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) (latticeEmbed K α + x))
      = {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.indicator (fun _ => 1) := by
    funext α
    by_cases h : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)
    · have h' : α ∈ {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : α ∉ {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [← Equiv.tsum_eq (latticeEquiv K)]
  simp only [latticeEquiv_coe]
  rw [hfun, ← tsum_subtype, ENNReal.tsum_set_one]
  exact_mod_cast count_encard_le x r

open scoped Classical in
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- **Lower bound of Lemma 3.5** (Blichfeldt). For a totally real field of degree `d` and `X ≥ 0`,
`X^d / √Δ_K ≤ |B⁺(X)|`. Proof: the multiplicity `g(y) = #{ℓ ∈ L : ℓ + y ∈ S}` of the radius-`X/2`
box `S` satisfies `∫_F g = vol S = X^d` (fundamental-domain decomposition) and `g(y) ≤ |B⁺(X)|`
pointwise (`count`), so `X^d ≤ |B⁺(X)| · vol F = |B⁺(X)| · √Δ_K`. -/
theorem boxAdd_card_ge {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card := by
  set r : NNReal := ⟨X / 2, by positivity⟩ with hr
  have hcoe : (r : ℝ) = X / 2 := by rw [hr]; rfl
  have hr2 : 2 * (r : ℝ) = X := by rw [hcoe]; ring
  set S := convexBodyLT K (fun _ => r) with hS
  set F := ZSpan.fundamentalDomain (latticeBasis K) with hFdef
  have hfund : IsAddFundamentalDomain (mixedEmbedding.integerLattice K) F volume :=
    fundamentalDomain_integerLattice K
  haveI : MeasurableVAdd (mixedEmbedding.integerLattice K) (mixedSpace K) :=
    inferInstanceAs (MeasurableVAdd (mixedEmbedding.integerLattice K).toAddSubgroup _)
  haveI : VAddInvariantMeasure (mixedEmbedding.integerLattice K) (mixedSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (mixedEmbedding.integerLattice K).toAddSubgroup _ _)
  have hSmeas : MeasurableSet S := by
    rw [hS, convexBodyLT]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  set f : mixedSpace K → ENNReal := S.indicator (fun _ => 1) with hf
  have hfmeas : Measurable f := measurable_const.indicator hSmeas
  -- discriminant positivity
  have hsqrtpos : 0 < Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [Real.sqrt_pos, abs_pos]
    exact_mod_cast NumberField.discr_ne_zero K
  -- covolume = √Δ
  have hFreal : (volume F).toReal = Real.sqrt |(NumberField.discr K : ℝ)| := by
    have hcov : ZLattice.covolume (mixedEmbedding.integerLattice K) volume
        = Real.sqrt |(NumberField.discr K : ℝ)| := by
      rw [mixedEmbedding.covolume_integerLattice, IsTotallyReal.nrComplexPlaces_eq_zero,
        pow_zero, one_mul]
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund, Measure.real]
  have hFne : volume F ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hFreal
    exact (ne_of_gt hsqrtpos) hFreal.symm
  -- volume of the box
  have hvolS : volume S = (2 : ENNReal) ^ d * (r : ENNReal) ^ d :=
    volume_convexBodyLT_const hd r
  -- the integral chain: vol S ≤ |B⁺(X)| · vol F
  have hSF : volume S ≤ (↑(boxAdd K X).card : ENNReal) * volume F := by
    have hint : ∫⁻ y, f y = volume S := by
      rw [hf, lintegral_indicator hSmeas, setLIntegral_one]
    have hkey : volume S
        = ∑' l : ↥(mixedEmbedding.integerLattice K), ∫⁻ y in F, f (l +ᵥ y) := by
      rw [← hint]; exact hfund.lintegral_eq_tsum'' f
    have hdecomp : volume S
        = ∫⁻ y in F, ∑' l : ↥(mixedEmbedding.integerLattice K), f (l +ᵥ y) := by
      rw [hkey]
      exact (lintegral_tsum fun l : ↥(mixedEmbedding.integerLattice K) =>
        (hfmeas.comp (measurable_const_vadd l)).aemeasurable).symm
    rw [hdecomp]
    calc ∫⁻ y in F, ∑' l : ↥(mixedEmbedding.integerLattice K), f (l +ᵥ y)
        ≤ ∫⁻ _ in F, (↑(boxAdd K X).card : ENNReal) := by
          refine lintegral_mono fun y => ?_
          have h := tsum_indicator_le y r
          rw [hr2] at h
          exact h
      _ = (↑(boxAdd K X).card : ENNReal) * volume F := by rw [setLIntegral_const]
  -- convert to reals
  have hSne : volume S ≠ ⊤ := by
    rw [hvolS]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hprodne : (↑(boxAdd K X).card : ENNReal) * volume F ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFne
  have hreal := (ENNReal.toReal_le_toReal hSne hprodne).mpr hSF
  rw [hvolS, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_natCast, hFreal, hcoe,
    ← mul_pow, show (2 : ℝ) * (X / 2) = X by ring] at hreal
  rw [div_le_iff₀ hsqrtpos]
  exact hreal

end SumProduct

#print axioms SumProduct.boxAddSet_finite
#print axioms SumProduct.count_encard_le
#print axioms SumProduct.boxAdd_card_ge
