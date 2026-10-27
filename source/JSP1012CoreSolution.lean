import ExactDegreeTower
import PolynomialBoundFromFields

/-!
# Hypothesis-free EP1207 assembly — SOURCE ONLY, NOT YET VERIFIED

This file must be compiled in the SINGLE audited NYLL Lean4.35.0-rc2 /
Mathlib06535612 environment after recompiling the local stable proof sources.
Stable and rc2 oleans must never be mixed. The exact-degree tower wrapper and
its NYLL import closure are still under independent build verification.

The theorem below introduces NO new assumption or axiom: it is an ordinary
application of the actual proof-bodied exact-degree endpoint. Until those
imports and this file compile, this remains only a candidate source, NOT a
completed theorem, whole-prize claim, submission, or upstream FC CI result.

Credits: LPZ26 for the mathematical argument; Naganori Yamaguchi/NYLL for the
Sawin tower formalization; the independently adapted licensed Formal Frontier
lower-box proof; Formal Conjectures for the exact P/free-set definitions.
-/

namespace JSP1012.CoreSolution

/-- Candidate assembly of the actual exact-degree field theorem with the
independently checked finite/parameter/eventual proof. Source-only until the
entire closure is checked under one rc2 toolchain. -/
theorem erdos_1207_expanded :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (FCBoundAdapter.P 2 n : ℝ) < (n : ℝ) ^ (1 - c) := by
  obtain ⟨Qset, hInfinite, hPrimes, hFields⟩ :=
    ClassFieldTower.Sawin.sawin_totally_real_exact_degree_tower_with_discr_bound
  apply PolynomialBoundFromFields.exists_eventual_polynomial_bound
    255255 (by decide) Qset hInfinite hPrimes
  intro i
  obtain ⟨F, instFieldF, instCharZeroF, instNumberFieldF, instTotallyRealF,
    hdegree, hroot, hdiscr, hsplit⟩ := hFields i
  exact ⟨F, instFieldF, instCharZeroF, instNumberFieldF, instTotallyRealF,
    hdegree, hdiscr, hsplit⟩

end JSP1012.CoreSolution

#print axioms JSP1012.CoreSolution.erdos_1207_expanded
