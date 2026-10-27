import FiniteCore
import SubsetWeights

/-!
# Exact finite residue-vector labels without quotient cardinality

A vector whose coordinates range below the listed radices has an injective
mixed-radix encoding below the product of those radices. Thus the LPZ finite
coset-counting step can use the actual linear residue vectors directly; it does
not need a separately postulated CRT quotient cardinality. Existence of the
prime-ideal residue maps, and the arithmetic interpretation of coordinate
equality, are still unproved number-field obligations.
-/

namespace JSP1012.Radix
open JSP1012

/-- Coordinate bounds also enforce the exact vector length. -/
def Bounded : List Nat → List Nat → Prop
  | [], [] => True
  | b :: bs, x :: xs => x < b ∧ Bounded bs xs
  | _, _ => False

instance boundedDecidable (bases digits : List Nat) : Decidable (Bounded bases digits) :=
  match bases, digits with
  | [], [] => isTrue True.intro
  | b :: bs, x :: xs =>
    if hx : x < b then
      match boundedDecidable bs xs with
      | isTrue ht => isTrue ⟨hx, ht⟩
      | isFalse ht => isFalse (fun h => ht h.2)
    else isFalse (fun h => hx h.1)
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)

/-- The first coordinate is the least significant digit. -/
def encode : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | b :: bs, x :: xs => x + b * encode bs xs

theorem bounded_length {bases digits : List Nat} (h : Bounded bases digits) :
    digits.length = bases.length := by
  induction bases generalizing digits with
  | nil => cases digits <;> simp_all [Bounded]
  | cons b bs ih =>
    cases digits with
    | nil => contradiction
    | cons x xs => simpa using congrArg Nat.succ (ih h.2)

/-- Every valid vector has a label strictly below the product of its bases. -/
theorem encode_lt_product {bases digits : List Nat} (h : Bounded bases digits) :
    encode bases digits < bases.prod := by
  induction bases generalizing digits with
  | nil => cases digits <;> simp_all [Bounded, encode]
  | cons b bs ih =>
    cases digits with
    | nil => contradiction
    | cons x xs =>
      have hx : x < b := h.1
      have ht : encode bs xs < bs.prod := ih h.2
      have hm := Nat.mul_le_mul_left b (show encode bs xs + 1 ≤ bs.prod by omega)
      simp only [Nat.mul_add, Nat.mul_one] at hm
      change x + b * encode bs xs < b * bs.prod
      omega

private theorem first_digit_mod (b x tail : Nat) (hx : x < b) :
    (x + b * tail) % b = x := by
  simp [Nat.add_mod, Nat.mod_eq_of_lt hx]

/-- Distinct bounded residue vectors never receive the same label. -/
theorem encode_injective {bases xs ys : List Nat}
    (hx : Bounded bases xs) (hy : Bounded bases ys)
    (heq : encode bases xs = encode bases ys) : xs = ys := by
  induction bases generalizing xs ys with
  | nil =>
    cases xs <;> cases ys <;> simp_all [Bounded]
  | cons b bs ih =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
      cases ys with
      | nil => contradiction
      | cons y ys =>
        have hxy : x = y := by
          have hm := congrArg (fun a => a % b) heq
          change (x + b * encode bs xs) % b = (y + b * encode bs ys) % b at hm
          rw [first_digit_mod b x _ hx.1, first_digit_mod b y _ hy.1] at hm
          exact hm
        subst y
        have hb : 0 < b := by have := hx.1; omega
        have hm : b * encode bs xs = b * encode bs ys := Nat.add_left_cancel heq
        have ht := Nat.eq_of_mul_eq_mul_left hb hm
        exact congrArg (x :: ·) (ih hx.2 hy.2 ht)

theorem encode_eq_iff {bases xs ys : List Nat}
    (hx : Bounded bases xs) (hy : Bounded bases ys) :
    encode bases xs = encode bases ys ↔ xs = ys :=
  ⟨encode_injective hx hy, fun h => congrArg (encode bases) h⟩

/-- No positivity assumptions are omitted: a radix zero with an actual digit
would contradict `Bounded`; radix one admits exactly its zero digit. -/
theorem encoded_label_bound (n : Nat) (A : Nat → Bool) (bases : List Nat)
    (digits : Nat → List Nat)
    (hbound : ∀ i, i < n → A i = true → Bounded bases (digits i)) :
    ∀ i, i < n → A i = true → encode bases (digits i) < bases.prod := by
  intro i hi hai
  exact encode_lt_product (hbound i hi hai)

/-- Same encoded fiber means precisely identical residue vectors, with the
selected distinct endpoint restrictions retained. -/
theorem sameFiber_iff {n : Nat} {A : Nat → Bool} {bases : List Nat}
    {digits : Nat → List Nat}
    (hbound : ∀ i, i < n → A i = true → Bounded bases (digits i))
    {i j : Nat} (hi : i < n) (hj : j < n) :
    Fibers.sameFiber A (fun a => encode bases (digits a)) i j = true ↔
      A i = true ∧ A j = true ∧ i ≠ j ∧ digits i = digits j := by
  constructor
  · intro h
    have hd : A i = true ∧ A j = true ∧ i ≠ j ∧
        encode bases (digits i) = encode bases (digits j) := by
      simpa [Fibers.sameFiber, Bool.and_eq_true, and_assoc] using h
    exact ⟨hd.1, hd.2.1, hd.2.2.1,
      encode_injective (hbound i hi hd.1) (hbound j hj hd.2.1) hd.2.2.2⟩
  · rintro ⟨hai, haj, hij, hd⟩
    simp [Fibers.sameFiber, hai, haj, hij, hd]

/-- The exact `Q^d` bin bound for a list of prime norms repeated `d` times. -/
theorem repeated_norm_label_bound (n d : Nat) (A : Nat → Bool) (norms : List Nat)
    (digits : Nat → List Nat)
    (hbound : ∀ i, i < n → A i = true →
      Bounded (Weights.repeatedNorms d norms) (digits i)) :
    ∀ i, i < n → A i = true →
      encode (Weights.repeatedNorms d norms) (digits i) < norms.prod ^ d := by
  intro i hi hai
  have h := encode_lt_product (hbound i hi hai)
  rw [Weights.repeatedNorms_product] at h
  exact h

/-- Fully composed same-residue collision lower bound, with genuine index pairs. -/
theorem residue_vector_collision_lower (n : Nat) (A : Nat → Bool)
    (bases : List Nat) (digits : Nat → List Nat)
    (hbound : ∀ i, i < n → A i = true → Bounded bases (digits i))
    (hsize : 2 * bases.prod ≤ countBelow n A) :
    (countBelow n A) ^ 2 ≤ 2 * bases.prod *
      pairCount n (Fibers.sameFiber A (fun i => encode bases (digits i))) :=
  same_fiber_lower n bases.prod A (fun i => encode bases (digits i))
    (encoded_label_bound n A bases digits hbound) hsize

end JSP1012.Radix

#print axioms JSP1012.Radix.encode_lt_product
#print axioms JSP1012.Radix.encode_injective
#print axioms JSP1012.Radix.sameFiber_iff
#print axioms JSP1012.Radix.repeated_norm_label_bound
#print axioms JSP1012.Radix.residue_vector_collision_lower

example : JSP1012.Radix.encode [5, 13, 5] [4, 12, 3] = 259 := by decide
example : JSP1012.Radix.Bounded [1, 5] [0, 4] := by decide
example : ¬ JSP1012.Radix.Bounded [0, 5] [0, 4] := by decide
example : JSP1012.Radix.encode [] [] < ([] : List Nat).prod := by decide
