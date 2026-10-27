import IdealWordProducts
import IdealSubsetWeights
import DivisorIncidence
import SignOverlap
import Mathlib.Data.List.Nodup

/-!
# Actual Boolean-word selection gives the extra ideal-product membership

STATUS: SOURCE-ONLY PREPARATION. This module has not yet been compiled.


The actual occurrence-selection list is a sublist of the actual ideal list.
Its product is exactly wordProduct, and its Nodup is derived from the explicit
Nodup hypothesis on the full list. Only AFTER these facts are established do
we pass to finsets to apply the verified coprime-ideal square-membership theorem.
Thus no ideal factor or equal numerical norm is silently deduplicated.

Actual subsetAllowed Boolean tests are proved to imply actual square-ideal
membership at every selected occurrence. No norm identity, root, valuation,
number-field construction, or global factorization is postulated here.
-/

noncomputable section

namespace JSP1012.IdealWordMembership

open scoped BigOperators Classical

/-- Keep exactly the true-selected occurrences, in their original list order.
As with wordProduct, omitted positions of a short word select nothing. -/
def selectedList {α : Type*} : List α → List Bool → List α
  | [], _ => []
  | _ :: _, [] => []
  | _ :: Is, false :: word => selectedList Is word
  | I :: Is, true :: word => I :: selectedList Is word

theorem selectedList_sublist {α : Type*} (Is : List α) (word : List Bool) :
    List.Sublist (selectedList Is word) Is := by
  induction Is generalizing word with
  | nil => exact List.Sublist.refl []
  | cons I Is ih =>
    cases word with
    | nil => exact List.nil_sublist _
    | cons sign word =>
      cases sign with
      | false => exact (ih word).cons I
      | true => exact (ih word).cons_cons I

theorem selectedList_nodup {α : Type*} (Is : List α) (word : List Bool)
    (hIs : Is.Nodup) : (selectedList Is word).Nodup :=
  (selectedList_sublist Is word).nodup hIs

/-- Exact selected-product identity, with no commutativity or length assumption. -/
theorem selectedList_prod {M : Type*} [Monoid M] (Is : List M) (word : List Bool) :
    (selectedList Is word).prod = IdealWordProducts.wordProduct Is word := by
  induction Is generalizing word with
  | nil => simp only [selectedList, List.prod_nil, IdealWordProducts.wordProduct]
  | cons I Is ih =>
    cases word with
    | nil => simp only [selectedList, List.prod_nil, IdealWordProducts.wordProduct]
    | cons sign word =>
      cases sign <;> simp only [selectedList, List.prod_cons, IdealWordProducts.wordProduct, ih]

theorem selectedList_toFinset_subset {α : Type*} [DecidableEq α]
    (Is : List α) (word : List Bool) : (selectedList Is word).toFinset ⊆ Is.toFinset := by
  intro I hI
  have hselected : I ∈ selectedList Is word := List.mem_toFinset.mp hI
  have hsub : selectedList Is word ⊆ Is := (selectedList_sublist Is word).subset
  exact List.mem_toFinset.mpr (hsub hselected)

section ActualIdeals

variable {R : Type*} [CommRing R]

/-- Actual square-membership bits, NOT separately assumed ideal-divisibility data. -/
def squareBits (Is : List (Ideal R)) (z : R) : List Bool := by
  classical
  exact Is.map (fun I => decide (z ∈ I ^ 2))

/-- Recursive Boolean compatibility of the actual square bits has its intended
actual ideal consequence at every selected occurrence. Full-word scope is explicit. -/
theorem square_memberships_of_subsetAllowed (Is : List (Ideal R)) (word : List Bool)
    (hlen : word.length = Is.length) (z : R)
    (hallowed : DivisorIncidence.subsetAllowed (squareBits Is z) word = true) :
    ∀ I ∈ selectedList Is word, z ∈ I ^ 2 := by
  classical
  induction Is generalizing word with
  | nil =>
    intro I hI
    simp only [selectedList, List.not_mem_nil] at hI
  | cons I Is ih =>
    cases word with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons sign word =>
      have htail : word.length = Is.length := Nat.succ.inj hlen
      have hstep :
          (if sign then decide (z ∈ I ^ 2) else true) &&
            DivisorIncidence.subsetAllowed (squareBits Is z) word = true := by
        change (if sign then decide (z ∈ I ^ 2) else true) &&
          DivisorIncidence.subsetAllowed (squareBits Is z) word = true at hallowed
        exact hallowed
      have hparts := Bool.and_eq_true_iff.mp hstep
      cases sign with
      | false =>
        intro J hJ
        exact ih word htail hparts.2 J hJ
      | true =>
        have hI : z ∈ I ^ 2 := of_decide_eq_true hparts.1
        intro J hJ
        rcases List.mem_cons.mp hJ with hJI | hJtail
        · simpa only [hJI] using hI
        · exact ih word htail hparts.2 J hJtail

/-- The required candidate-count membership bridge to the ACTUAL extra ideal
factor. Every finset product is converted back using proved Nodup identities. -/
theorem mem_product_mul_wordProduct (Is : List (Ideal R)) (word : List Bool)
    (hlen : word.length = Is.length) (hIs : Is.Nodup)
    (hcoprime : (Is.toFinset : Set (Ideal R)).Pairwise IsCoprime)
    (z : R) (hz : z ∈ Is.prod)
    (hallowed : DivisorIncidence.subsetAllowed (squareBits Is z) word = true) :
    z ∈ Is.prod * IdealWordProducts.wordProduct Is word := by
  classical
  have hselectedNodup := selectedList_nodup Is word hIs
  have htotal : (∏ I ∈ Is.toFinset, I) = Is.prod := by
    simpa only [List.map_id, id_eq] using List.prod_toFinset id hIs
  have hselected : (∏ I ∈ (selectedList Is word).toFinset, I) =
      IdealWordProducts.wordProduct Is word := by
    calc
      (∏ I ∈ (selectedList Is word).toFinset, I) = (selectedList Is word).prod := by
        simpa only [List.map_id, id_eq] using List.prod_toFinset id hselectedNodup
      _ = IdealWordProducts.wordProduct Is word := selectedList_prod Is word
  have hzFin : z ∈ ∏ I ∈ Is.toFinset, I := by rw [htotal]; exact hz
  have hsquares : ∀ I ∈ (selectedList Is word).toFinset, z ∈ I ^ 2 := by
    intro I hI
    exact square_memberships_of_subsetAllowed Is word hlen z hallowed I (List.mem_toFinset.mp hI)
  have hmem := IdealSubsetWeights.mem_total_mul_selected_of_squares
    Is.toFinset (selectedList Is word).toFinset (selectedList_toFinset_subset Is word)
    (fun I : Ideal R => I) hcoprime hzFin hsquares
  rw [htotal, hselected] at hmem
  exact hmem

/-- Every word supplied by the ACTUAL sign enumeration has the required length. -/
theorem mem_product_mul_wordProduct_of_mem_signWords (Is : List (Ideal R)) (word : List Bool)
    (hword : word ∈ SignOverlap.signWords Is.length) (hIs : Is.Nodup)
    (hcoprime : (Is.toFinset : Set (Ideal R)).Pairwise IsCoprime)
    (z : R) (hz : z ∈ Is.prod)
    (hallowed : DivisorIncidence.subsetAllowed (squareBits Is z) word = true) :
    z ∈ Is.prod * IdealWordProducts.wordProduct Is word :=
  mem_product_mul_wordProduct Is word ((SignOverlap.mem_signWords_iff Is.length word).mp hword)
    hIs hcoprime z hz hallowed

end ActualIdeals

example : selectedList ([5, 5, 13] : List Nat) [true, true, false] = [5, 5] := by decide
example : selectedList ([] : List Nat) [] = [] := by decide

end JSP1012.IdealWordMembership

#print axioms JSP1012.IdealWordMembership.selectedList_sublist
#print axioms JSP1012.IdealWordMembership.selectedList_prod
#print axioms JSP1012.IdealWordMembership.square_memberships_of_subsetAllowed
#print axioms JSP1012.IdealWordMembership.mem_product_mul_wordProduct
