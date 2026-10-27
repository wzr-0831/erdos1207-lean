import PrimeAmplification

/-!
# Finite distinct amplification factors from an unbounded predicate

Verified Std-only finite selection. This has no global prime-existence axiom:
`hlarge` is an explicit unboundedness hypothesis, to be instantiated with the
actual fixed infinite common split-prime set from the field construction.
-/

namespace JSP1012.PrimeSelection

def maxList : List Nat → Nat
  | [] => 0
  | p :: ps => max p (maxList ps)

theorem member_le_maxList {ps : List Nat} {p : Nat} (hp : p ∈ ps) : p ≤ maxList ps := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with h | h
    · subst p
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem exists_distinct_list (P : Nat → Prop)
    (hlarge : ∀ B : Nat, ∃ p : Nat, B < p ∧ P p) :
    ∀ k : Nat, ∃ ps : List Nat, ps.length = k ∧ ps.Nodup ∧
      (∀ p, p ∈ ps → P p ∧ 5 ≤ p) := by
  intro k
  induction k with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨ps, hlen, hnd, hprop⟩ := ih
    obtain ⟨p, hp, hpP⟩ := hlarge (max (maxList ps) 4)
    have hpmax : maxList ps < p := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hp
    have hp4 : 4 < p := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hp
    have hpnot : p ∉ ps := by
      intro hmem
      have hle := member_le_maxList hmem
      omega
    refine ⟨p :: ps, by simp [hlen], List.nodup_cons.mpr ⟨hpnot, hnd⟩, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · subst q
      exact ⟨hpP, by omega⟩
    · exact hprop q h

theorem exists_amplifying_list (P : Nat → Prop)
    (hlarge : ∀ B : Nat, ∃ p : Nat, B < p ∧ P p) (C : Nat) :
    ∃ ps : List Nat, ps.length = C + 3 ∧ ps.Nodup ∧
      (∀ p, p ∈ ps → P p) ∧
      C * (ps.map (fun p => p + 1)).prod ≤ 2 ^ ps.length * ps.prod := by
  obtain ⟨ps, hlen, hnd, hprop⟩ := exists_distinct_list P hlarge (C + 3)
  exact ⟨ps, hlen, hnd, (fun p hp => (hprop p hp).1),
    PrimeAmplification.amplification C ps (fun p hp => (hprop p hp).2) hlen⟩

end JSP1012.PrimeSelection

#print axioms JSP1012.PrimeSelection.exists_distinct_list
#print axioms JSP1012.PrimeSelection.exists_amplifying_list
