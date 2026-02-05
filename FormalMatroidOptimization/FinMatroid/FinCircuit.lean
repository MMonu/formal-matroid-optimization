import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit

import FormalMatroidOptimization.FinMatroid.Basic

/-!
# Circuits of finite Matroids

## Main Definitions / Proofs

* `FinDep M` Dependents sets of a finite matroid `M` are subsets of the ground set, that are not
  independent.

* `IsFinCircuit M` Circuits of a finite matroid `M` are minimal dependent sets.
-/

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

lemma FinDep_exists_FinCircuit_subset {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {X : Finset α} (hX : FinDep M X) : ∃ C ⊆ X, IsFinCircuit M C :=
  exists_minimal_le_of_wellFoundedLT (FinDep M) X hX

open Finset in
lemma FinCircuit_ex_mem_nin_Indep {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {I C : Finset α} (hI : M.Indep I) (hC : IsFinCircuit M C) : ∃ c, c ∈ C \ I := by
  by_contra!
  simp only [mem_sdiff, not_and, Decidable.not_not, ← subset_iff] at this
  grind only [FinDep, M.indep_subset hI this, hC.1]

open Finset in
lemma FinIndep_exchange_mem_circuit_FinIndep {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {e f : α} {I C : Finset α} (hI : M.Indep I) (hC : IsFinCircuit M C) (heI : e ∈ C \ I)
    (hCe : C ⊆ (insert e I)) (hf : f ∈ C \ {e}) : M.Indep (insert e I \ {f}) := by
  refine (FinIndep_iff_Indep M (insert e I \ {f})).mpr ?_
  have he_cl : e ∈ M.toMatroid.closure I := by
    refine (Matroid.Indep.mem_closure_iff ((FinIndep_iff_Indep M I).mp hI)).mpr ?_
    left
    simpa [coe_insert] using ((FinDep_iff_Dep M (insert e I)).mp (by
      constructor
      · by_contra; grind only [FinDep, M.indep_subset this hCe, hC.1]
      · rw [insert_eq e I]
        refine union_subset ?_ (M.subset_ground hI)
        grind only [mem_sdiff, hC.1.2, subset_iff, singleton_subset_iff]))
  rw [mem_sdiff] at heI hf
  have := Matroid.IsCircuit.eq_fundCircuit_of_subset ((FinCircuit_iff_Circuit M C).mp hC)
    ((FinIndep_iff_Indep M I).mp hI) (by rwa [← coe_subset, coe_insert e I] at hCe)
  rw [coe_sdiff, coe_insert, coe_singleton]
  exact ((Matroid.Indep.mem_fundCircuit_iff ((FinIndep_iff_Indep M I).mp hI)) he_cl heI.2).mp
    (by rw [← mem_coe, this] at hf; exact hf.1)
