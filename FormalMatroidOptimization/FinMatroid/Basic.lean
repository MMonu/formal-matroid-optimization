import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Tactic

def IndepSystem.HereditaryProperty {α : Type*} (P : Finset α → Prop) : Prop :=
  ∀ ⦃X Y⦄, P X → Y ⊆ X → P Y

def IndepSystem.AugmentationProperty {α : Type*} [DecidableEq α] (P : Finset α → Prop) : Prop :=
  ∀ ⦃X Y⦄, P X → P Y → X.card > Y.card → ∃ x ∈ X, x ∉ Y ∧ P (insert x Y)

open Finset in
lemma IndepSystem.augmentation_of_succ {α : Type*} [DecidableEq α] (P : Finset α → Prop)
    (h₁ : IndepSystem.HereditaryProperty P)
    (h₂ : ∀ ⦃X Y⦄, P X → P Y → #X = #Y + 1 → ∃ x ∈ X, x ∉ Y ∧ P (insert x Y)) :
    IndepSystem.AugmentationProperty P := by
  intro X Y
  refine Finset.induction_on X ?_ ?_
  · simp
  · intro z Z hz ih hPzZ hPY hzZY
    rw [card_insert_of_notMem hz, gt_iff_lt, Nat.lt_add_one_iff_lt_or_eq] at hzZY
    cases hzZY with
    | inl h =>
      obtain ⟨x, hx⟩ := ih (h₁ hPzZ (subset_insert z Z)) hPY h
      exact ⟨x, (by simp only [mem_insert, hx, or_true]), hx.right⟩
    | inr h => exact h₂ hPzZ hPY (by simp [h, hz])

structure IndepSystem (α : Type*) where
  /-- Independent system has a ground set `E` -/
  (E : Finset α)
  /-- Independent system has a predicate `Indep` defining its independent sets -/
  (Indep : Finset α → Prop)
  /-- `Indep` should be decidable -/
  (indep_dec : DecidablePred Indep)
  /-- The empty set is `Indep`endent -/
  (indep_empty : Indep ∅)
  /-- For any `Indep`endent set `X`, all its subsets are also `Indep`endent -/
  (indep_subset : IndepSystem.HereditaryProperty Indep)
  /-- All `Indep`endent sets are subsets of the ground set -/
  (subset_ground : ∀ ⦃X⦄, Indep X → X ⊆ E)

instance {α : Type*} {F : IndepSystem α} : DecidablePred F.Indep := F.indep_dec

structure FinMatroid (α : Type*) [DecidableEq α] extends IndepSystem α where
  /-- For any `Indep`endent sets `X` and `Y` with `Y` smaller than `X`, there exists an element in
  `X` not in `Y` with `Y ∪ {x}` `Indep`endent -/
  (indep_aug : IndepSystem.AugmentationProperty Indep)

instance {α : Type*} [DecidableEq α] : Coe (FinMatroid α) (IndepSystem α) :=
  ⟨FinMatroid.toIndepSystem⟩

def IndepToMatroidUp {α : Type*} [DecidableEq α] (F : IndepSystem α)
    (h : IndepSystem.AugmentationProperty F.Indep) :
  FinMatroid α := { toIndepSystem := F, indep_aug := h }

def FinMatroid.toMatroid {α : Type*} [DecidableEq α] (M : FinMatroid α) :
  Matroid α := by
  let Indep' (X : Set α) : Prop := ∃ hX : X.Finite, M.Indep hX.toFinset
  refine IndepMatroid.matroid (IndepMatroid.ofFinite (M.E.finite_toSet)
    (Indep') (?_) (?_) (?_) (?_))
  · simp [Indep', M.indep_empty]
  · intro I J ⟨hJ_Fin, hJ_Indep⟩ hIJ
    have hI_Fin := Set.Finite.subset hJ_Fin hIJ
    exact ⟨hI_Fin, M.indep_subset hJ_Indep (Set.Finite.toFinset_subset_toFinset.mpr hIJ)⟩
  · intro I J ⟨hI_Fin, hI_Indep⟩ ⟨hJ_Fin, hJ_Indep⟩ hcard
    have : hI_Fin.toFinset.card < hJ_Fin.toFinset.card := by
      rwa [← Set.ncard_eq_toFinset_card I hI_Fin, ← Set.ncard_eq_toFinset_card J hJ_Fin]
    obtain ⟨x, hxJ, hxI, hx⟩ := M.indep_aug hJ_Indep hI_Indep this
    refine ⟨x, (Set.Finite.mem_toFinset hJ_Fin).mp hxJ, ?_, ?_⟩
    · rwa [← Set.Finite.mem_toFinset hI_Fin]
    · have hxI' : (insert x I).Finite := Set.finite_insert.mpr hI_Fin
      exact ⟨hxI', by rwa [Set.Finite.toFinset_insert]⟩
  · intro I ⟨hI_Fin, hI_Indep⟩
    exact Set.Finite.toFinset_subset.mp (M.subset_ground hI_Indep)

lemma toMatroid_FinIndep_iff {α : Type*} [DecidableEq α] (M : FinMatroid α) (I : Set α) :
  M.toMatroid.Indep I ↔ ∃ hI : (I : Set α).Finite, M.Indep hI.toFinset := Iff.rfl

lemma FinIndep_iff_Indep {α : Type*} [DecidableEq α] (M : FinMatroid α) (I : Finset α) :
  M.Indep I ↔ M.toMatroid.Indep I := by
  simp only [toMatroid_FinIndep_iff, Set.toFinite_toFinset, Finset.toFinset_coe,
  Finset.finite_toSet, exists_const]

def IsFinMatroid {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] : Prop :=
  IndepSystem.AugmentationProperty (F.Indep)
