import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Degree-sum saturation for the actual split-prime factors

STATUS: SOURCE-ONLY PREPARATION. This version has not yet been compiled.
No Lean process is authorized during the current memory gate. The declarations
below require an actual coordinated successful build before being reported as
verified mathematical results.

The intended adapter starts with the precise finite-ideal output of the Sawin
tower: `d` DISTINCT maximal ideals containing the rational prime `q`, where
`d=[K:ℚ]`. It does not assume that this list is exhaustive or that the residue
degrees are one. Injection into ALL primes over `(q)`, positivity of every
ramification/inertia contribution, and the actual fundamental degree-sum
identity force every such contribution to be one. This proves the residue
norm/cardinality needed by the finite-field root adapter.

No NYLL import, tower existence, custom axiom, or assumed degree-one property
occurs here. Module finiteness, flatness, integrality and the Dedekind/Noetherian
conditions are the actual instances for `𝓞 K`; the only field hypothesis is
`[NumberField K]`. The finite all-primes-over enumeration is constructed from
Mathlib's proved finiteness theorem.
-/

noncomputable section

namespace JSP1012.SplitDegreeSaturation

open NumberField
open scoped BigOperators

/-- A finite positive-natural sum bounded by the number of its terms can only
have unit terms. This includes the empty ambient type without special pleading. -/
theorem weight_eq_one_of_sum_le_card {β : Type*} [Fintype β]
    (weight : β → ℕ) (hpositive : ∀ b, 0 < weight b)
    (htotal : (∑ b, weight b) ≤ Fintype.card β) : ∀ b, weight b = 1 := by
  classical
  intro b
  have hremaining : (Finset.univ.erase b).card ≤
      ∑ c ∈ Finset.univ.erase b, weight c := by
    calc
      (Finset.univ.erase b).card = ∑ _c ∈ Finset.univ.erase b, (1 : ℕ) := by simp
      _ ≤ ∑ c ∈ Finset.univ.erase b, weight c := by
        apply Finset.sum_le_sum
        intro c hc
        exact Nat.succ_le_of_lt (hpositive c)
  have hsplit := Finset.add_sum_erase Finset.univ weight (Finset.mem_univ b)
  have hcard := Finset.card_erase_add_one (Finset.mem_univ b)
  have hb := hpositive b
  simp only [Finset.card_univ] at hcard
  omega

/-- If a finite family injects into all ambient indices and its cardinality
already equals their positive total weight, every ambient weight is one.
Exhaustiveness of the injected family is a conclusion, not an assumption. -/
theorem weight_eq_one_of_injection {α β : Type*} [Fintype α] [Fintype β]
    (embed : α → β) (hinjective : Function.Injective embed)
    (weight : β → ℕ) (hpositive : ∀ b, 0 < weight b)
    (htotal : (∑ b, weight b) = Fintype.card α) : ∀ b, weight b = 1 := by
  have hcard := Fintype.card_le_of_injective embed hinjective
  apply weight_eq_one_of_sum_le_card weight hpositive
  rw [htotal]
  exact hcard

/-- A proper prime ideal containing a rational prime lies over its actual
principal ideal in `ℤ`, rather than merely lying above some unspecified prime. -/
theorem liesOver_span_of_mem {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (P : Ideal (𝓞 K)) (hP : P.IsMaximal)
    (hqmem : (q : 𝓞 K) ∈ P) : P.LiesOver (Ideal.span {(q : ℤ)}) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : P.IsMaximal := hP
  have hle : Ideal.span {(q : ℤ)} ≤ P.under ℤ := by
    apply (Ideal.span_singleton_le_iff_mem (P.under ℤ)).mpr
    change algebraMap ℤ (𝓞 K) (q : ℤ) ∈ P
    simpa only [map_natCast] using hqmem
  have hbase : (Ideal.span {(q : ℤ)}).IsMaximal := inferInstance
  have hunder : (P.under ℤ).IsPrime := inferInstance
  exact ⟨hbase.eq_of_le hunder.ne_top hle⟩

/-- The FULL fundamental sum saturates: every listed ideal has both
ramification index and inertia degree equal to one. There is no Galois
hypothesis and the finite list need not be assumed exhaustive. -/
theorem indices_eq_one_of_degree_many_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    ∀ P ∈ factors, P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  letI : base.IsMaximal := Int.ideal_span_isMaximal_of_prime q
  letI : Fintype (base.primesOver (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite base (𝓞 K)).fintype
  let embed : ↥factors → base.primesOver (𝓞 K) := fun P =>
    ⟨P.val, ⟨(hfactors P.val P.property).1.isPrime,
      liesOver_span_of_mem hq P.val (hfactors P.val P.property).1
        (hfactors P.val P.property).2⟩⟩
  have hinjective : Function.Injective embed := by
    intro P Q hPQ
    apply Subtype.ext
    exact congrArg (fun t : base.primesOver (𝓞 K) => t.val) hPQ
  let weight : base.primesOver (𝓞 K) → ℕ := fun P =>
    P.val.ramificationIdx ℤ * P.val.inertiaDeg ℤ
  have hpositive : ∀ P, 0 < weight P := by
    intro P
    exact Nat.mul_pos (P.val.ramificationIdx_pos ℤ) (P.val.inertiaDeg_pos ℤ)
  have htotal : (∑ P, weight P) = Fintype.card ↥factors := by
    have hfundamental := Ideal.sum_ramification_inertia_eq_finrank base (𝓞 K)
    simpa only [weight, Fintype.card_coe, hcard, RingOfIntegers.rank] using hfundamental
  have hunit := weight_eq_one_of_injection embed hinjective weight hpositive htotal
  intro P hP
  letI : P.IsMaximal := (hfactors P hP).1
  have hprod : P.ramificationIdx ℤ * P.inertiaDeg ℤ = 1 :=
    hunit (embed ⟨P, hP⟩)
  have hfpositive : 0 < P.inertiaDeg ℤ := P.inertiaDeg_pos ℤ
  have helower : 1 ≤ P.ramificationIdx ℤ := Nat.succ_le_of_lt (P.ramificationIdx_pos ℤ)
  have hflower : P.inertiaDeg ℤ ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P.inertiaDeg ℤ) helower
  have hf : P.inertiaDeg ℤ = 1 := by omega
  have he : P.ramificationIdx ℤ = 1 := by simpa only [hf, Nat.mul_one] using hprod
  exact ⟨he, hf⟩

theorem inertiaDeg_eq_one_of_degree_many_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) : P.inertiaDeg ℤ = 1 :=
  (indices_eq_one_of_degree_many_factors hq factors hcard hfactors P hP).2

/-- Actual ideal norm equals the rational prime, using Mathlib's proved
prime-norm / residue-degree identity rather than an assumed preservation law. -/
theorem absNorm_eq_prime_of_degree_many_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) : P.absNorm = q := by
  letI : P.IsMaximal := (hfactors P hP).1
  letI : P.LiesOver (Ideal.span {(q : ℤ)}) :=
    liesOver_span_of_mem hq P (hfactors P hP).1 (hfactors P hP).2
  have hf := inertiaDeg_eq_one_of_degree_many_factors hq factors hcard hfactors P hP
  have hnorm := Ideal.pow_inertiaDeg (R := 𝓞 K) q P
  rw [hf, pow_one] at hnorm
  exact hnorm.symm

/-- The actual residue quotient has cardinality `q`, in the exact `Nat.card`
form required by `PrimeResidue.quotient_exists_root_of_natCard`. -/
theorem quotient_card_eq_prime_of_degree_many_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) : Nat.card ((𝓞 K) ⧸ P) = q := by
  have hn := absNorm_eq_prime_of_degree_many_factors hq factors hcard hfactors P hP
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hn

/-- Finiteness of the actual quotient follows from its proved positive
cardinality, so the finite-field adapter needs no additional finiteness axiom. -/
theorem quotient_finite_of_degree_many_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P)
    (P : Ideal (𝓞 K)) (hP : P ∈ factors) : Finite ((𝓞 K) ⧸ P) := by
  apply Nat.finite_of_card_ne_zero
  rw [quotient_card_eq_prime_of_degree_many_factors hq factors hcard hfactors P hP]
  exact hq.ne_zero

end JSP1012.SplitDegreeSaturation

#print axioms JSP1012.SplitDegreeSaturation.weight_eq_one_of_sum_le_card
#print axioms JSP1012.SplitDegreeSaturation.liesOver_span_of_mem
#print axioms JSP1012.SplitDegreeSaturation.indices_eq_one_of_degree_many_factors
#print axioms JSP1012.SplitDegreeSaturation.absNorm_eq_prime_of_degree_many_factors
#print axioms JSP1012.SplitDegreeSaturation.quotient_card_eq_prime_of_degree_many_factors
