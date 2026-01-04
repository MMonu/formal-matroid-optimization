import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sublists

def IndepSystem.HereditaryProperty {α : Type*} (P : Finset α → Bool) : Prop :=
  ∀ ⦃X Y⦄, P X → Y ⊆ X → P Y

def IndepSystem.AugmentationProperty {α : Type*} [DecidableEq α] (P : Finset α → Bool) : Prop :=
  ∀ ⦃X Y⦄, P X → P Y → X.card > Y.card → ∃ x ∈ X, x ∉ Y ∧ P (insert x Y)

structure IndepSystem (α : Type*) where
  /-- Independent system has a ground set `E` -/
  (E : Finset α)
  /-- Independent system has a predicate `Indep` defining its independent sets -/
  (Indep : Finset α → Bool)
  /-- The empty set is `Indep`endent -/
  (indep_empty : Indep ∅)
  /-- For any `Indep`endent set `X`, all its subsets are also `Indep`endent -/
  (indep_subset : IndepSystem.HereditaryProperty Indep)
  /-- All `Indep`endent sets are subsets of the ground set -/
  (subset_ground : ∀ ⦃X⦄, Indep X → X ⊆ E)

structure FinMatroid (α : Type*) [DecidableEq α] extends IndepSystem α where
  /-- For any `Indep`endent sets `X` and `Y` with `Y` smaller than `X`, there exists an element in
  `X` not in `Y` with `Y ∪ {x}` `Indep`endent -/
  (indep_aug : IndepSystem.AugmentationProperty Indep)

noncomputable def FinMatroid.toMatroid {α : Type*} [DecidableEq α] (M : FinMatroid α) :
  Matroid α := by
  let Indep' (X : Set α) : Prop := ∃ hX : X.Finite, M.Indep hX.toFinset
  refine IndepMatroid.matroid (IndepMatroid.ofFinite (M.E.finite_toSet)
    (Indep') (?_) (?_) (?_) (?_))
  · simp [Indep', M.indep_empty]
  · intro I J ⟨hJ_Fin, hJ_Indep⟩ hIJ
    have hI_Fin : I.Finite := by exact Set.Finite.subset hJ_Fin hIJ
    use hI_Fin
    have : hI_Fin.toFinset ⊆ hJ_Fin.toFinset := Set.Finite.toFinset_subset_toFinset.mpr hIJ
    exact M.indep_subset hJ_Indep this
  · intro I J ⟨hI_Fin, hI_Indep⟩ ⟨hJ_Fin, hJ_Indep⟩ hcard
    have : hI_Fin.toFinset.card < hJ_Fin.toFinset.card := by
      rwa [← Set.ncard_eq_toFinset_card I hI_Fin, ← Set.ncard_eq_toFinset_card J hJ_Fin]
    obtain ⟨x, hxJ, hxI, hx⟩ := M.indep_aug hJ_Indep hI_Indep this
    use x
    constructor
    · exact (Set.Finite.mem_toFinset hJ_Fin).mp hxJ
    · constructor
      · rwa [← Set.Finite.mem_toFinset hI_Fin]
      · have hxI' : (insert x I).Finite := by exact Set.finite_insert.mpr hI_Fin
        use hxI'
        rwa [Set.Finite.toFinset_insert hxI']
  · intro I ⟨hI_Fin, hI_Indep⟩
    exact Set.Finite.toFinset_subset.mp (M.subset_ground hI_Indep)

/-- Greedily select elements from a list, right to left -/
def GreedySelect {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) : List α :=
  match lst with
  | []      => []
  | x :: xs =>
    if P (insert x (GreedySelect P xs).toFinset) then
      x :: (GreedySelect P xs)
    else
      GreedySelect P xs

open List in
theorem GreedySelect.Sublist {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) :
  GreedySelect P lst <+ lst := by
  induction lst with
  | nil => simp [GreedySelect]
  | cons x xs ih =>
    simp [GreedySelect]
    by_cases h : P (insert x (GreedySelect P xs).toFinset) = true
    · simpa [if_pos h]
    · simp [if_neg h, ih]

namespace GreedySelectExample

def P : Finset (Fin 3) → Bool := fun X ↦ match X.card with
| 0 => true
| 1 => true
| 2 => true
| _ => false

def lst : List (Fin 3) := [3, 2, 1]

#eval GreedySelect P lst

end GreedySelectExample

open Classical in
noncomputable def GreedyMin {α β : Type*} [DecidableEq α] [LinearOrder β] (F : IndepSystem α)
  (c : α → β) : List α :=
  GreedySelect F.Indep (F.E.toList.mergeSort (fun a b ↦ decide (c a ≤ c b)))

lemma LE_lift {α β : Type*} [LinearOrder β] (lst : List α) (c : α → β) :
  ((lst.mergeSort (fun a b ↦ decide (c a ≤ c b))).map c).SortedLE := by
  let r (a b : α) : Prop := c a ≤ c b
  let h_total : IsTotal α r := ⟨fun a b ↦ le_total (c a) (c b)⟩
  let h_trans : IsTrans α r := ⟨fun a b d ha hb ↦ le_trans ha hb⟩
  have h' : ∀ a b, r a b → c a ≤ c b := by intro a b hrab; unfold r at hrab; assumption
  have := (List.pairwise_mergeSort' r lst).map c h'
  exact List.Pairwise.sortedLE this

#check List.Pairwise.sublist
#check List.isChain_map

theorem GreedyMin.sorted {α β : Type*} [DecidableEq α] [LinearOrder β] {F : IndepSystem α}
  {c : α → β} : ((GreedyMin F c).map c).SortedLE := by
  let r (a b : α) : Prop := c a ≤ c b
  let h_total : IsTotal α r := ⟨fun a b ↦ le_total (c a) (c b)⟩
  let h_trans : IsTrans α r := ⟨fun a b d ha hb ↦ le_trans ha hb⟩
  have := LE_lift F.E.toList c
  unfold GreedyMin
  rw [List.sortedLE_iff_isChain, List.isChain_map] at *
  rw [List.isChain_iff_pairwise] at *
  refine List.Pairwise.sublist (?_) this
  exact GreedySelect.Sublist F.Indep (F.E.toList.mergeSort fun a b ↦ decide (c a ≤ c b))
