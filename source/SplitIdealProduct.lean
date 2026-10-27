import SplitDegreeSaturation
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Actual ideal factor products and distinct split-prime coordinates

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
It requires a coordinated successful compiler run and axiom audit before any
of its declarations may be reported as verified milestones.

Distinct maximal ideals are proved coprime. Their product is their actual
intersection, so containment of the rational prime puts `(q)` inside that
product. Degree saturation gives norm `q` for each factor; actual norm
multiplicativity and the principal-ideal norm theorem give equal positive
norms. Comparable equal-norm ideals are proved equal by an actual Dedekind
cofactor and multiplicative norm cancellation, not a postulated norm-injection
property. No factorization, exhaustion, or residue-degree hypothesis is added.

The final source lemmas keep factors over different rational primes distinct
by their actual contractions to `ℤ`, including injection of all prime/factor
occurrence coordinates. No NYLL module is imported or executed.
-/

noncomputable section

namespace JSP1012.SplitIdealProduct

open NumberField
open scoped BigOperators

/-- Positive equal norms distinguish comparable ideals, by a derived Dedekind
cofactor. This does NOT claim that absolute norm distinguishes arbitrary ideals. -/
theorem eq_of_le_of_positive_absNorm_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Infinite R] (I J : Ideal R) (hle : I ≤ J)
    (hpositive : 0 < I.absNorm) (hnorm : I.absNorm = J.absNorm) : I = J := by
  obtain ⟨H, hH⟩ := Ideal.dvd_iff_le.mpr hle
  have hJpositive : 0 < J.absNorm := by
    rw [← hnorm]
    exact hpositive
  have hmul : J.absNorm * H.absNorm = J.absNorm * 1 := by
    calc
      J.absNorm * H.absNorm = I.absNorm := by rw [hH, map_mul]
      _ = J.absNorm := hnorm
      _ = J.absNorm * 1 := (Nat.mul_one _).symm
  have hHnorm : H.absNorm = 1 := Nat.eq_of_mul_eq_mul_left hJpositive hmul
  have hHtop : H = ⊤ := Ideal.absNorm_eq_one_iff.mp hHnorm
  rw [hHtop, ← Ideal.one_eq_top, mul_one] at hH
  exact hH

/-- Distinct ideals in the finite list are genuinely coprime because they are
maximal; numerical norm equality is neither used nor confused with equality. -/
theorem factors_pairwise_coprime {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (factors : Finset (Ideal (𝓞 K)))
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (factors : Set (Ideal (𝓞 K))).Pairwise IsCoprime := by
  intro P hP Q hQ hPQ
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact (hfactors P hP).1.coprime_of_ne (hfactors Q hQ).1 hPQ

/-- The rational-prime principal ideal is actually contained in the product,
using the coprime-product/intersection identity and membership in every factor. -/
theorem span_prime_le_product_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (factors : Finset (Ideal (𝓞 K)))
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    Ideal.span {(q : 𝓞 K)} ≤ ∏ P ∈ factors, P := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (factors_pairwise_coprime factors hfactors)]
  apply le_iInf
  intro P
  apply le_iInf
  intro hP
  exact (Ideal.span_singleton_le_iff_mem P).mpr (hfactors P hP).2

/-- The actual product norm, retaining every distinct ideal even when its
numerical norm agrees with the norms of the other factors. -/
theorem absNorm_product_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (∏ P ∈ factors, P).absNorm = q ^ Module.finrank ℚ K := by
  calc
    (∏ P ∈ factors, P).absNorm = ∏ _P ∈ factors, q := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro P hP
      exact SplitDegreeSaturation.absNorm_eq_prime_of_degree_many_factors
        hq factors hcard hfactors P hP
    _ = q ^ Module.finrank ℚ K := by simp only [Finset.prod_const, hcard]

/-- The actual product factorization follows without assuming exhaustiveness
or importing a prime-factorization claim from the tower source. -/
theorem product_factors_eq_span_prime {K : Type*} [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) (factors : Finset (Ideal (𝓞 K)))
    (hcard : factors.card = Module.finrank ℚ K)
    (hfactors : ∀ P ∈ factors, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    (∏ P ∈ factors, P) = Ideal.span {(q : 𝓞 K)} := by
  have hprincipal : (Ideal.span {(q : 𝓞 K)}).absNorm = q ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hproduct := absNorm_product_factors hq factors hcard hfactors
  have hpositive : 0 < (Ideal.span {(q : 𝓞 K)}).absNorm := by
    rw [hprincipal]
    exact pow_pos hq.pos _
  exact (eq_of_le_of_positive_absNorm_eq
    (Ideal.span {(q : 𝓞 K)}) (∏ P ∈ factors, P)
    (span_prime_le_product_factors factors hfactors) hpositive
    (hprincipal.trans hproduct.symm)).symm

/-- Factors over distinct rational primes cannot coincide: actual contraction
identifies their respective integer principal prime ideals. -/
theorem ideals_over_distinct_primes_ne {K : Type*} [Field K] [NumberField K]
    {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (P Q : Ideal (𝓞 K)) (hP : P.IsMaximal) (hQ : Q.IsMaximal)
    (hmemP : (q₁ : 𝓞 K) ∈ P) (hmemQ : (q₂ : 𝓞 K) ∈ Q) : P ≠ Q := by
  intro hPQ
  have hleft := SplitDegreeSaturation.liesOver_span_of_mem hq₁ P hP hmemP
  have hright := SplitDegreeSaturation.liesOver_span_of_mem hq₂ Q hQ hmemQ
  have hbase : (Ideal.span {(q₁ : ℤ)} : Ideal ℤ) = Ideal.span {(q₂ : ℤ)} :=
    hleft.over.trans ((congrArg (fun I : Ideal (𝓞 K) => I.under ℤ) hPQ).trans hright.over.symm)
  have hnorm := congrArg (fun I : Ideal ℤ => I.absNorm) hbase
  apply hne
  simpa only [Ideal.absNorm_span_natCast, Module.finrank_self, pow_one] using hnorm

/-- Finite ideal-factor families for distinct rational primes are disjoint. -/
theorem factor_families_disjoint {K : Type*} [Field K] [NumberField K]
    {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (factors₁ factors₂ : Finset (Ideal (𝓞 K)))
    (h₁ : ∀ P ∈ factors₁, P.IsMaximal ∧ (q₁ : 𝓞 K) ∈ P)
    (h₂ : ∀ P ∈ factors₂, P.IsMaximal ∧ (q₂ : 𝓞 K) ∈ P) :
    Disjoint factors₁ factors₂ := by
  apply Finset.disjoint_left.mpr
  intro P hP₁ hP₂
  exact ideals_over_distinct_primes_ne hq₁ hq₂ hne P P
    (h₁ P hP₁).1 (h₂ P hP₂).1 (h₁ P hP₁).2 (h₂ P hP₂).2 rfl

/-- All `(rational prime, factor ideal)` coordinates remain distinct when
flattened to actual ideals. No equal numerical ideal norms are deduplicated. -/
theorem sigma_factor_injective {K : Type*} [Field K] [NumberField K]
    (qs : Finset ℕ) (factors : ℕ → Finset (Ideal (𝓞 K)))
    (hprime : ∀ q ∈ qs, q.Prime)
    (hfactors : ∀ q ∈ qs, ∀ P ∈ factors q, P.IsMaximal ∧ (q : 𝓞 K) ∈ P) :
    Function.Injective (fun z : Σ q : ↥qs, ↥(factors q.val) => z.2.val) := by
  classical
  intro a b hab
  rcases a with ⟨qa, Pa⟩
  rcases b with ⟨qb, Pb⟩
  have hqval : qa.val = qb.val := by
    by_contra hne
    exact ideals_over_distinct_primes_ne
      (hprime qa.val qa.property) (hprime qb.val qb.property) hne Pa.val Pb.val
      (hfactors qa.val qa.property Pa.val Pa.property).1
      (hfactors qb.val qb.property Pb.val Pb.property).1
      (hfactors qa.val qa.property Pa.val Pa.property).2
      (hfactors qb.val qb.property Pb.val Pb.property).2 hab
  have hq : qa = qb := Subtype.ext hqval
  cases hq
  have hP : Pa = Pb := Subtype.ext hab
  cases hP
  rfl

end JSP1012.SplitIdealProduct

#print axioms JSP1012.SplitIdealProduct.eq_of_le_of_positive_absNorm_eq
#print axioms JSP1012.SplitIdealProduct.factors_pairwise_coprime
#print axioms JSP1012.SplitIdealProduct.product_factors_eq_span_prime
#print axioms JSP1012.SplitIdealProduct.ideals_over_distinct_primes_ne
#print axioms JSP1012.SplitIdealProduct.sigma_factor_injective
