import Mathlib.Tactic

import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.FinMatroid.FinBases
import FormalMatroidOptimization.Greedy.Basic
import FormalMatroidOptimization.List.Greedy
import Mathlib.Order.Minimal

namespace FinMatroid

#check Finset.sort

noncomputable def selectRel {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) [DecidablePred F.Indep] :
    List α := Greedy.selectRel F.Indep r F.E.toList

noncomputable def selectRel' {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) [DecidablePred F.Indep] :
    List α := List.Greedy.selectRel F.Indep r F.E.toList

def weight {α : Type*} (c : α → ℝ) (X : Finset α) : ℝ :=
  Finset.sum X c

def weight_is_maximum {α : Type*} [DecidableEq α] (I : IndepSystem α) [DecidablePred I.Indep]
  (c : α → ℝ) (F : Finset α) : Prop := ∀ X : Finset α, Maximal I.Indep X → weight c X ≤ weight c F

def weightRel {α : Type*} (c : α → ℝ) : α → α → Prop := fun x y ↦ c x ≤ c y

noncomputable section

instance {α : Type*} (c : α → ℝ) : DecidableRel (weightRel c) :=
  Classical.decRel (weightRel c)

end

instance {α : Type*} (c : α → ℝ) : IsTotal α (weightRel c) := by
  refine { total := ?_ }
  intro a b
  exact Std.IsLinearPreorder.le_total (c a) (c b)

instance {α : Type*} (c : α → ℝ) : IsTrans α (weightRel c) := by
  refine { trans := ?_ }
  intro a b d
  exact fun a_1 a_2 ↦ Std.IsPreorder.le_trans (c a) (c b) (c d) a_1 a_2

noncomputable def Greedy_set {α : Type*} [DecidableEq α] (I : IndepSystem α)
  [DecidablePred I.Indep] (c : α → ℝ) : Finset α :=
    (selectRel (weightRel c) (I : IndepSystem α)).toFinset

/-
lemma Greedy_maxweight {α : Type*} [DecidableEq α] (M : FinMatroid α) [DecidablePred M.Indep]
  (B : Finset α) (hB: IsFinBase M B) (c : α → ℝ) :
  ∀ i ∈ [B.card],
  c ((B.toList.mergeSort (fun a b ↦ weightRel c a b))[i]!) ≤
    c ((Greedy_set M c).toList[i]!) := by sorry
-/

theorem Matroid_then_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
  IsFinMatroid F →
  ∀ c : α → ℝ,
      Maximal F.Indep (Greedy_set F c) ∧
      weight_is_maximum F c (Greedy_set F c) := by
  intro h c
  constructor
  · have : ∀ ⦃s t : Finset α⦄, F.Indep t → s ⊆ t → F.Indep s := by
      intro X Y hX
      apply F.indep_subset
      grind only
    rw [Finset.maximal_iff_forall_insert (P := F.Indep) this]
    constructor
    · -- indep
      have : F.Indep ([].toFinset) := by simp only [List.toFinset_nil, F.indep_empty]
      have := Greedy.selectRel_internal_indep
        (P := F.Indep) (r := weightRel c) (xs := F.E.toList) (ys := []) this
      exact ((fun a ↦ this) ∘ fun a ↦ α) α
    · -- max
      intro x hxnot
      by_cases hx : x ∈ F.E.toList
      · exact Greedy.selectRel_internal_maximal
          (P := F.Indep) (r := weightRel c) (xs := F.E.toList) (ys := []) x hx hxnot
      · intro hxInd
        have hxSubset : insert x (Greedy_set F c) ⊆ F.E := F.subset_ground hxInd
        have : x ∈ F.E := hxSubset (by simp)
        have : x ∈ F.E.toList := Finset.mem_toList.mpr this
        contradiction
  · -- max weight
    unfold weight_is_maximum
    intro X hX
    unfold IsFinMatroid at h
    set M := IndepToMatroidUp (F := F) (h := h) with hM
    have : F.Indep = M.Indep := Set.setOf_inj.mp rfl
    rw [this] at hX
    set GB := Greedy_set F c with hGB
    unfold Greedy_set at hGB
    unfold selectRel at hGB
    have hxs : (F.E.toList).Nodup := by sorry
    have ha : ∀ (x y : α), x ∈ F.E.toList → y ∈ F.E.toList →
        weightRel c x y ∧ weightRel c y x → x = y := by
      intro x y hx hy
      unfold weightRel
      --exact le_antisymm_iff.mpr (c x) (c y)
      sorry
    rw [Greedy.selectRel_eq_list_selectRel (P:= F.Indep) (F.indep_subset)
      (r := weightRel c) (hxs) (ha)] at hGB
    --mergeSort_toFinset_eq
    sorry

theorem Matroid_if_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
  ∀ c : α → ℝ,
      Maximal F.Indep (Greedy_set F c) ∧
      weight_is_maximum F c (Greedy_set F c) →
  IsFinMatroid F := by
  sorry

theorem Matroid_iff_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
  IsFinMatroid F ↔
  ∀ c : α → ℝ,
      Maximal F.Indep (Greedy_set F c) ∧
      weight_is_maximum F c (Greedy_set F c) := by
  sorry

end FinMatroid
