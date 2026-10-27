import QuotientDigits
import MixedRadix
import SignOverlap

/-!
# Actual signed quotient vectors and their mixed-radix labels

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.
Its direct local dependencies are QuotientDigits, MixedRadix and SignOverlap.
MixedRadix lives in ../proof and also requires FiniteCore / SubsetWeights and
their transitive Std modules in the coordinated compiler's import path.

Each coordinate records an actual finite quotient, its proved cardinality,
and one fixed integral root representative (no root relation is needed for
vector equality). Every label is built from actual signed quotient digits.
Only FULL-LENGTH Boolean words are used in public range/equality lemmas.

The digit enumeration is not assumed to preserve addition, multiplication,
or numeric zero. Equality is checked in the real quotient FIRST. Equal mixed
radix labels are equivalent to Boolean sign compatibility for the actual
coordinate differences, with the SAME root representative at both points.
No fallback-digit global injectivity claim is made.
-/

noncomputable section

namespace JSP1012.SignedResidueVectors

universe u

/-- Actual finite quotient data. The separate root and local norm implications
can later be instantiated from SplitResidueData; they are not assumed here. -/
structure Coordinate (R : Type u) [CommRing R] where
  I : Ideal R
  q : Nat
  finite : Finite (R ⧸ I)
  hcard : Nat.card (R ⧸ I) = q
  r : R

namespace Coordinate

variable {R : Type u} [CommRing R]

/-- The chosen actual quotient digit of the signed linear form. -/
def digit (c : Coordinate R) (sign : Bool) (x y : R) : Nat := by
  letI : Finite (R ⧸ c.I) := c.finite
  exact QuotientDigits.signedDigit c.I c.q c.hcard c.r sign x y

theorem digit_lt (c : Coordinate R) (sign : Bool) (x y : R) :
    c.digit sign x y < c.q := by
  letI : Finite (R ⧸ c.I) := c.finite
  exact QuotientDigits.signedDigit_lt c.I c.q c.hcard c.r sign x y

theorem equal_digits_iff_zero_difference (c : Coordinate R) (sign : Bool)
    (x y x' y' : R) :
    c.digit sign x y = c.digit sign x' y' ↔
      QuotientDigits.signedLinear c.I c.r sign (x - x') (y - y') = 0 := by
  letI : Finite (R ⧸ c.I) := c.finite
  exact QuotientDigits.equal_signedDigits_iff_zero_difference c.I c.q c.hcard c.r sign x y x' y'

/-- Minus permissions come first, matching SignOverlap.compatible's convention. -/
def permissions (c : Coordinate R) (dx dy : R) : Bool × Bool := by
  classical
  exact (decide (QuotientDigits.signedLinear c.I c.r false dx dy = 0),
    decide (QuotientDigits.signedLinear c.I c.r true dx dy = 0))

theorem permission_eq_true_iff (c : Coordinate R) (sign : Bool) (dx dy : R) :
    (if sign then (c.permissions dx dy).2 else (c.permissions dx dy).1) = true ↔
      QuotientDigits.signedLinear c.I c.r sign dx dy = 0 := by
  classical
  cases sign <;> simp [permissions]

end Coordinate

section Vectors

variable {R : Type u} [CommRing R]

/-- Actual quotient cardinalities are the mixed-radix bases. -/
def bases (cs : List (Coordinate R)) : List Nat := cs.map Coordinate.q

/-- Simultaneous coordinate/word recursion; public lemmas require full words. -/
def digits : List (Coordinate R) → List Bool → R → R → List Nat
  | [], _, _, _ => []
  | _ :: _, [], _, _ => []
  | c :: cs, sign :: word, x, y => c.digit sign x y :: digits cs word x y

/-- Actual local signs permitted for one difference pair. -/
def signPermissions (cs : List (Coordinate R)) (dx dy : R) : List (Bool × Bool) :=
  cs.map (fun c => c.permissions dx dy)

@[simp] theorem bases_length (cs : List (Coordinate R)) : (bases cs).length = cs.length := by
  simp only [bases, List.length_map]

@[simp] theorem signPermissions_length (cs : List (Coordinate R)) (dx dy : R) :
    (signPermissions cs dx dy).length = cs.length := by
  simp only [signPermissions, List.length_map]

/-- Every full word gives a genuinely bounded residue vector. -/
theorem digits_bounded (cs : List (Coordinate R)) (word : List Bool)
    (hlen : word.length = cs.length) (x y : R) :
    Radix.Bounded (bases cs) (digits cs word x y) := by
  induction cs generalizing word with
  | nil => exact True.intro
  | cons c cs ih =>
    cases word with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons sign word =>
      have htail : word.length = cs.length := Nat.succ.inj hlen
      exact ⟨c.digit_lt sign x y, ih word htail⟩

/-- No coordinate is silently lost when the actual word has the required length. -/
theorem digits_length (cs : List (Coordinate R)) (word : List Bool)
    (hlen : word.length = cs.length) (x y : R) :
    (digits cs word x y).length = cs.length := by
  have h := Radix.bounded_length (digits_bounded cs word hlen x y)
  simpa only [bases_length] using h

/-- Actual mixed-radix label, without an assumed CRT cardinality. -/
def label (cs : List (Coordinate R)) (word : List Bool) (x y : R) : Nat :=
  Radix.encode (bases cs) (digits cs word x y)

theorem label_lt (cs : List (Coordinate R)) (word : List Bool)
    (hlen : word.length = cs.length) (x y : R) :
    label cs word x y < (bases cs).prod :=
  Radix.encode_lt_product (digits_bounded cs word hlen x y)

/-- The actual full-vector equality is equivalent to the exact local Boolean
compatibility conjunction, recursively retaining every coordinate occurrence. -/
theorem digits_eq_iff_compatible (cs : List (Coordinate R)) (word : List Bool)
    (hlen : word.length = cs.length) (x y x' y' : R) :
    digits cs word x y = digits cs word x' y' ↔
      SignOverlap.compatible (signPermissions cs (x - x') (y - y')) word = true := by
  induction cs generalizing word with
  | nil =>
    cases word with
    | nil => simp only [digits, signPermissions, List.map_nil, SignOverlap.compatible]
    | cons sign word => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons c cs ih =>
    cases word with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons sign word =>
      have htail : word.length = cs.length := Nat.succ.inj hlen
      simp only [digits, List.cons.injEq, signPermissions, List.map_cons,
        SignOverlap.compatible, Bool.and_eq_true]
      rw [Coordinate.equal_digits_iff_zero_difference, ih word htail]
      exact and_congr (Coordinate.permission_eq_true_iff c sign (x - x') (y - y')).symm Iff.rfl

/-- The required encode/sign equivalence. Bounds and encode injectivity are
proved from the actual quotient data; no global fallback-label claim is used. -/
theorem label_eq_iff_compatible (cs : List (Coordinate R)) (word : List Bool)
    (hlen : word.length = cs.length) (x y x' y' : R) :
    label cs word x y = label cs word x' y' ↔
      SignOverlap.compatible (signPermissions cs (x - x') (y - y')) word = true := by
  unfold label
  rw [Radix.encode_eq_iff (digits_bounded cs word hlen x y)
    (digits_bounded cs word hlen x' y')]
  exact digits_eq_iff_compatible cs word hlen x y x' y'

/-- The actual enumerated sign words meet the full-length prerequisite. -/
theorem label_lt_of_mem_signWords (cs : List (Coordinate R)) (word : List Bool)
    (hword : word ∈ SignOverlap.signWords cs.length) (x y : R) :
    label cs word x y < (bases cs).prod :=
  label_lt cs word ((SignOverlap.mem_signWords_iff cs.length word).mp hword) x y

end Vectors
end JSP1012.SignedResidueVectors

#print axioms JSP1012.SignedResidueVectors.Coordinate.equal_digits_iff_zero_difference
#print axioms JSP1012.SignedResidueVectors.digits_bounded
#print axioms JSP1012.SignedResidueVectors.label_lt
#print axioms JSP1012.SignedResidueVectors.digits_eq_iff_compatible
#print axioms JSP1012.SignedResidueVectors.label_eq_iff_compatible
