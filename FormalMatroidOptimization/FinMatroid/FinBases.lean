import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Tactic
import FormalMatroidOptimization.FinMatroid.Basic

def IsFinBase {α : Type*} [DecidableEq α] (F : IndepSystem α) :=
  Maximal (F.Indep)

open Finset in
lemma exists_IsFinBase_superset {α : Type*} [DecidableEq α] {F : IndepSystem α} {I : Finset α}
    (h : F.Indep I) : ∃ B, IsFinBase F B ∧ I ⊆ B := by
  set s := F.E.powerset.filter (fun X ↦ F.Indep X ∧ I ⊆ X) with hs
  obtain ⟨B, hB₁, hB₂⟩ := exists_le_maximal s (show I ∈ s by simp [hs, h, F.subset_ground])
  refine ⟨B, ?_, hB₁⟩
  rw [maximal_iff_forall_gt, mem_filter] at hB₂
  obtain ⟨⟨hB₃, hB₄, hB₅⟩, hB₆⟩ := hB₂
  simp only [IsFinBase]
  rw [maximal_iff_forall_gt]
  refine ⟨hB₄, ?_⟩
  intro B' hB'₁
  by_contra hc
  have : B' ∈ s := by
    rw [mem_filter, mem_powerset]
    refine ⟨F.subset_ground hc, hc, ?_⟩
    exact trans_of _ hB₅ (subset_of_ssubset hB'₁)
  exact hB₆ hB'₁ this

lemma IsFinBase_iff_IsBase {α : Type*} [DecidableEq α] (M : FinMatroid α) (B : Finset α) :
  IsFinBase M B ↔ Matroid.IsBase M.toMatroid B := by
  simp only [Matroid.isBase_iff_maximal_indep]
  unfold IsFinBase Maximal
  constructor
  · intro ⟨hB_FIndep, hB_max⟩
    constructor
    · exact (FinIndep_iff_Indep M B).mp hB_FIndep
    · intro X hX_Indep hBX
      obtain ⟨hX_finite, hX_FIndep⟩ := (toMatroid_FinIndep_iff M X).mp hX_Indep
      have : X = hX_finite.toFinset := Eq.symm (Set.Finite.coe_toFinset hX_finite)
      rw [this] at hBX ⊢
      exact hB_max hX_FIndep hBX
  · intro ⟨hB_Indep, hB_max⟩
    constructor
    · exact (FinIndep_iff_Indep M B).mpr hB_Indep
    · intro X hX_FIndep hBX
      have hX_Indep := (FinIndep_iff_Indep M X).mp hX_FIndep
      exact Finset.le_iff_subset.mpr (hB_max hX_Indep hBX)
