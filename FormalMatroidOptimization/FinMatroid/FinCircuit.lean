import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Tactic
import FormalMatroidOptimization.FinMatroid.IndepSystem

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
  · intro ⟨h1, h2⟩
    constructor
    · exact (FinDep_iff_Dep M C).mp h1
    · intro D hD DsubC
      have Dfinite := Set.Finite.subset C.finite_toSet DsubC
      let Dfin := Dfinite.toFinset
      --have := (FinDep_iff_Dep M (Dfin)).mpr hD
      have : Dfin = D := Set.Finite.coe_toFinset Dfinite
      rw [←this] at hD DsubC ⊢
      have h := (FinDep_iff_Dep M Dfin).mpr hD
      exact Set.le_iff_subset.mpr (h2 h DsubC)
  · intro ⟨h1, h2⟩
    constructor
    · exact (FinDep_iff_Dep M C).mpr h1
    · intro D hD DsubC
      have h := (FinDep_iff_Dep M D).mp hD
      exact Finset.le_iff_subset.mpr (h2 h DsubC)
