import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Tactic

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
