import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Tactic
import FormalMatroidOptimization.FinMatroid.IndepSystem

def IsFinBase {α : Type*} [DecidableEq α] (M : FinMatroid α) :=
  Maximal (M.Indep)

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
