import Std

/-!
# Explicit finite sign-vector overlap bounds

The first Boolean in each coordinate's data permits the minus sign (`false`),
and the second permits the plus sign (`true`). We enumerate all Boolean words,
prove that this enumeration is complete and duplicate-free, and count the
compatible words by filtering that enumeration. Thus the overlap bound counts
actual sign vectors, rather than a postulated product of coordinate counts.

This is only the finite sign-choice step toward LPZ26 §3. It makes no claim
about prime-square divisibility, CRT, number fields, or the whole EP1207 result.
-/

namespace JSP1012.SignOverlap

/-- Every Boolean word of length `n`, in a fixed recursive order. -/
def signWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (signWords n).map (false :: ·) ++ (signWords n).map (true :: ·)

/-- Membership in the explicit enumeration means exactly the prescribed length. -/
theorem mem_signWords_iff (n : Nat) (word : List Bool) :
    word ∈ signWords n ↔ word.length = n := by
  induction n generalizing word with
  | zero => cases word <;> simp [signWords]
  | succ n ih =>
    cases word with
    | nil => simp [signWords]
    | cons b word =>
      cases b <;> simp [signWords, List.mem_append, List.mem_map, ih]

/-- No sign vector is counted more than once. -/
theorem signWords_nodup (n : Nat) : (signWords n).Nodup := by
  induction n with
  | zero => simp [signWords]
  | succ n ih =>
    have hmap (b : Bool) : ((signWords n).map (b :: ·)).Nodup := by
      exact List.Pairwise.map (b :: ·)
        (fun _ _ hne heq => hne (List.cons.inj heq).2) ih
    apply List.nodup_append.mpr
    refine ⟨hmap false, hmap true, ?_⟩
    intro a ha b hb heq
    obtain ⟨u, hu, hua⟩ := List.mem_map.mp ha
    obtain ⟨v, hv, hvb⟩ := List.mem_map.mp hb
    rw [← hua, ← hvb] at heq
    have hhead : false = true := (List.cons.inj heq).1
    cases hhead

/-- The duplicate-free enumeration contains exactly `2^n` sign vectors. -/
theorem signWords_length (n : Nat) : (signWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signWords, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

/-- A word is compatible if it has exactly one permitted sign per coordinate. -/
def compatible : List (Bool × Bool) → List Bool → Bool
  | [], [] => true
  | c :: cs, b :: bs => (if b then c.2 else c.1) && compatible cs bs
  | _, _ => false

/-- The actual enumeration restricted to compatible sign vectors. -/
def compatibleWords (data : List (Bool × Bool)) : List (List Bool) :=
  (signWords data.length).filter (compatible data)

/-- Number of compatible sign vectors in the explicit enumeration. -/
def compatibleCount (data : List (Bool × Bool)) : Nat :=
  (signWords data.length).countP (compatible data)

theorem compatibleCount_eq_filtered_length (data : List (Bool × Bool)) :
    compatibleCount data = (compatibleWords data).length :=
  List.countP_eq_length_filter

theorem mem_compatibleWords_iff (data : List (Bool × Bool)) (word : List Bool) :
    word ∈ compatibleWords data ↔
      word.length = data.length ∧ compatible data word = true := by
  simp only [compatibleWords, List.mem_filter, mem_signWords_iff]

theorem compatibleWords_nodup (data : List (Bool × Bool)) :
    (compatibleWords data).Nodup :=
  List.Pairwise.filter _ (signWords_nodup data.length)

/-- Number of coordinates where both signs are allowed. -/
def bothCount : List (Bool × Bool) → Nat
  | [] => 0
  | c :: cs => bothCount cs + if c.1 && c.2 then 1 else 0

/-- The exponent is exactly the ordinary finite count of both-allowed coordinates. -/
theorem bothCount_eq_countP (data : List (Bool × Bool)) :
    bothCount data = data.countP (fun c => c.1 && c.2) := by
  induction data with
  | nil => rfl
  | cons c cs ih => simp [bothCount, List.countP_cons, ih]

@[simp] theorem compatibleCount_nil : compatibleCount [] = 1 := by decide

/-- The recurrence is derived from the actual enumeration, not used as a definition. -/
theorem compatibleCount_cons (c : Bool × Bool) (cs : List (Bool × Bool)) :
    compatibleCount (c :: cs) =
      (if c.1 then compatibleCount cs else 0) +
      (if c.2 then compatibleCount cs else 0) := by
  rcases c with ⟨minus, plus⟩
  cases minus <;> cases plus <;>
    simp [compatibleCount, signWords, List.countP_append, List.countP_map,
      Function.comp_def, compatible]

/-- Each ambiguous coordinate contributes at most a factor of two. -/
theorem compatibleCount_le_two_pow_both (data : List (Bool × Bool)) :
    compatibleCount data ≤ 2 ^ bothCount data := by
  induction data with
  | nil => decide
  | cons c cs ih =>
    rcases c with ⟨minus, plus⟩
    cases minus <;> cases plus <;>
      simp [compatibleCount_cons, bothCount, Nat.pow_succ] <;> omega

/-- The same bound stated directly as the cardinality of the filtered enumeration. -/
theorem compatibleWords_length_le (data : List (Bool × Bool)) :
    (compatibleWords data).length ≤ 2 ^ bothCount data := by
  rw [← compatibleCount_eq_filtered_length]
  exact compatibleCount_le_two_pow_both data

/-- A coordinate with no permitted sign annihilates the whole overlap. -/
theorem compatibleCount_zero_of_dead_coordinate (data : List (Bool × Bool))
    (hdead : (false, false) ∈ data) : compatibleCount data = 0 := by
  induction data with
  | nil => simp at hdead
  | cons c cs ih =>
    rcases List.mem_cons.mp hdead with h | h
    · subst c
      simp [compatibleCount_cons]
    · rw [compatibleCount_cons, ih h]
      simp

/-- The underlying enumeration itself is empty when a coordinate has no choice. -/
theorem compatibleWords_eq_nil_of_dead_coordinate (data : List (Bool × Bool))
    (hdead : (false, false) ∈ data) : compatibleWords data = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw [← compatibleCount_eq_filtered_length]
  exact compatibleCount_zero_of_dead_coordinate data hdead

/-- If every coordinate has a permitted sign, the power-of-two bound is sharp. -/
theorem compatibleCount_eq_of_no_dead_coordinate (data : List (Bool × Bool))
    (hno : (false, false) ∉ data) :
    compatibleCount data = 2 ^ bothCount data := by
  induction data with
  | nil => decide
  | cons c cs ih =>
    have htail : (false, false) ∉ cs := fun h => hno (List.mem_cons.mpr (Or.inr h))
    have hhead : c ≠ (false, false) := by
      intro h
      exact hno (List.mem_cons.mpr (Or.inl h.symm))
    have heq := ih htail
    rcases c with ⟨minus, plus⟩
    cases minus <;> cases plus <;>
      simp_all [compatibleCount_cons, bothCount, Nat.pow_succ] <;> omega

/-- In particular, allowing both signs everywhere gives all `2^n` words. -/
theorem all_allowing_equality (n : Nat) :
    compatibleCount (List.replicate n (true, true)) = 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp [List.replicate_succ, compatibleCount_cons, ih, Nat.pow_succ]
    omega

/-- There is one empty word; the zero-dimensional overlap is not zero. -/
example : compatibleWords [] = [[]] := by decide

/-- One forced sign, one ambiguous sign, then one forced sign gives two words. -/
example : compatibleWords [(true, false), (true, true), (false, true)] =
    [[false, false, true], [false, true, true]] := by decide

example : bothCount [(true, false), (true, true), (false, true)] = 1 := by decide

/-- A single dead coordinate makes the actual filtered enumeration empty. -/
example : compatibleWords [(true, true), (false, false), (true, false)] = [] := by
  decide

example : compatibleCount (List.replicate 4 (true, true)) = 16 := by decide

end JSP1012.SignOverlap

#print axioms JSP1012.SignOverlap.mem_signWords_iff
#print axioms JSP1012.SignOverlap.signWords_nodup
#print axioms JSP1012.SignOverlap.bothCount_eq_countP
#print axioms JSP1012.SignOverlap.compatibleCount_eq_filtered_length
#print axioms JSP1012.SignOverlap.compatibleCount_le_two_pow_both
#print axioms JSP1012.SignOverlap.compatibleCount_zero_of_dead_coordinate
#print axioms JSP1012.SignOverlap.compatibleCount_eq_of_no_dead_coordinate
#print axioms JSP1012.SignOverlap.all_allowing_equality
