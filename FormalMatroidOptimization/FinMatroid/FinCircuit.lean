import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit

import FormalMatroidOptimization.FinMatroid.Basic

def FinDep {α : Type*} [DecidableEq α] (M : FinMatroid α) (D : Finset α) :
  Prop := ¬M.Indep D ∧ D ⊆ M.E

lemma FinDep_iff_Dep {α : Type*} [DecidableEq α] (M : FinMatroid α) (D : Finset α) :
  FinDep M D ↔ Matroid.Dep M.toMatroid D := by
  refine and_congr_left_iff.mpr ?_
  intro
  refine Iff.not ?_
  exact FinIndep_iff_Indep M D

def IsFinCircuit {α : Type*} [DecidableEq α] (M : FinMatroid α) :=
  Minimal (FinDep M)

lemma FinCircuit_iff_Circuit {α : Type*} [DecidableEq α] (M : FinMatroid α) (C : Finset α) :
  IsFinCircuit M C ↔ Matroid.IsCircuit M.toMatroid C := by
  constructor
  · intro ⟨hC_FDep, hC_min⟩
    constructor
    · exact (FinDep_iff_Dep M C).mp hC_FDep
    · intro D hD_Dep hDC
      have D_finite := Set.Finite.subset C.finite_toSet hDC
      have : D = D_finite.toFinset := Eq.symm (Set.Finite.coe_toFinset D_finite)
      rw [this] at hD_Dep hDC ⊢
      exact hC_min ((FinDep_iff_Dep M D_finite.toFinset).mpr hD_Dep) hDC
  · intro ⟨hC_Dep, hC_min⟩
    constructor
    · exact (FinDep_iff_Dep M C).mpr hC_Dep
    · intro D hD_FDep hDC
      exact hC_min ((FinDep_iff_Dep M D).mp hD_FDep) hDC
