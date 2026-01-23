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

def weight {α β : Type*} [AddCommMonoid β] (c : α → β) (X : Finset α) : β := Finset.sum X c

def weight_is_maximum {α β : Type*} [DecidableEq α] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedAddMonoid β] (F : IndepSystem α) [DecidablePred F.Indep] (c : α → β) (Y : Finset α) :
    Prop :=
  ∀ X : Finset α, Maximal F.Indep X → weight c X ≤ weight c Y

def weightRel {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] (c : α → β) :
    α → α → Prop := fun x y ↦ c x ≤ c y

noncomputable section

instance {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] (c : α → β) :
    DecidableRel (weightRel c) := Classical.decRel (weightRel c)

end

instance {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] (c : α → β) :
    IsTotal α (weightRel c) := by
  refine { total := ?_ }
  intro a b
  exact Std.IsLinearPreorder.le_total (c a) (c b)

instance {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] (c : α → β) :
    IsTrans α (weightRel c) := by
  refine { trans := ?_ }
  intro a b d
  exact fun a_1 a_2 ↦ Std.IsPreorder.le_trans (c a) (c b) (c d) a_1 a_2

noncomputable def Greedy_set {α β : Type*} [DecidableEq α] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedAddMonoid β] (F : IndepSystem α) [DecidablePred F.Indep] (c : α → β) : Finset α :=
  (selectRel (weightRel c) (F : IndepSystem α)).toFinset

/-
lemma Greedy_maxweight {α : Type*} [DecidableEq α] (M : FinMatroid α) [DecidablePred M.Indep]
  (B : Finset α) (hB: IsFinBase M B) (c : α → ℝ) :
  ∀ i ∈ [B.card],
  c ((B.toList.mergeSort (fun a b ↦ weightRel c a b))[i]!) ≤
    c ((Greedy_set M c).toList[i]!) := by sorry
-/

-- theorem Matroid_then_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
--   IsFinMatroid F →
--   ∀ c : α → β ,
--       Maximal F.Indep (Greedy_set F c) ∧
--       weight_is_maximum F c (Greedy_set F c) := by
--   intro h c
--   constructor
--   · have : ∀ ⦃s t : Finset α⦄, F.Indep t → s ⊆ t → F.Indep s := by
--       intro X Y hX
--       apply F.indep_subset
--       grind only
--     rw [Finset.maximal_iff_forall_insert (P := F.Indep) this]
--     constructor
--     · -- indep
--       have : F.Indep ([].toFinset) := by simp only [List.toFinset_nil, F.indep_empty]
--       have := Greedy.selectRel_internal_indep
--         (P := F.Indep) (r := weightRel c) (xs := F.E.toList) (ys := []) this
--       exact ((fun a ↦ this) ∘ fun a ↦ α) α
--     · -- max
--       intro x hxnot
--       by_cases hx : x ∈ F.E.toList
--       · exact Greedy.selectRel_internal_maximal
--           (P := F.Indep) (r := weightRel c) (xs := F.E.toList) (ys := []) x hx hxnot
--       · intro hxInd
--         have hxSubset : insert x (Greedy_set F c) ⊆ F.E := F.subset_ground hxInd
--         have : x ∈ F.E := hxSubset (by simp)
--         have : x ∈ F.E.toList := Finset.mem_toList.mpr this
--         contradiction
--   · -- max weight
--     unfold weight_is_maximum
--     intro X hX
--     unfold IsFinMatroid at h
--     set M := IndepToMatroidUp (F := F) (h := h) with hM
--     have : F.Indep = M.Indep := Set.setOf_inj.mp rfl
--     rw [this] at hX
--     set GB := Greedy_set F c with hGB
--     unfold Greedy_set at hGB
--     unfold selectRel at hGB
--     have hxs : (F.E.toList).Nodup := by sorry
--     have ha : ∀ (x y : α), x ∈ F.E.toList → y ∈ F.E.toList →
--         weightRel c x y ∧ weightRel c y x → x = y := by
--       intro x y hx hy
--       unfold weightRel
--       --exact le_antisymm_iff.mpr (c x) (c y)
--       sorry
--     rw [Greedy.selectRel_eq_list_selectRel (P:= F.Indep) (F.indep_subset)
--       (r := weightRel c) (hxs) (ha)] at hGB
--     --mergeSort_toFinset_eq
--     sorry

theorem indep {α : Type*} [DecidableEq α] (P : Finset α → Prop) :
    (∀ X Y, P X → P Y → X.card = Y.card + 1 → ∃ x ∈ X, x ∉ Y ∧ P (insert x Y)) →
    IndepSystem.AugmentationProperty P := by
  intro h X Y hX hY hc
  sorry

lemma exists_eq_insert_of_card_succ {α : Type*} [DecidableEq α] {X Y : Finset α} (hXY : X ⊆ Y)
    (hcard : Y.card = X.card + 1) : ∃ x, x ∈ Y ∧ x ∉ X ∧ Y = insert x X:= by
  have h : (Y \ X).card = 1 := by grind
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
  use x
  have hx' := (Finset.mem_sdiff.mp (Finset.eq_singleton_iff_unique_mem.mp hx).left)
  refine ⟨hx'.left, hx'.right, ?_⟩
  ext y
  constructor
  · intro h
    rw [Finset.mem_insert]
    rw [← Finset.sdiff_union_inter Y X, Finset.mem_union] at h
    cases h with
    | inl h' => simp only [hx, Finset.mem_singleton] at h'; left; exact h'
    | inr h' => right; grind
  · intro h
    rw [Finset.mem_insert] at h
    cases h with
    | inl h' => rw [h']; exact hx'.left
    | inr h' => exact hXY h'

open Finset List in
theorem Matroid_of_Greedy {α β : Type*} [DecidableEq α] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedAddMonoid β] (F : IndepSystem α) [DecidablePred F.Indep]
    (h : ∀ c : α → ℕ, Maximal F.Indep (Greedy_set F c) ∧ weight_is_maximum F c (Greedy_set F c)) :
    IsFinMatroid F := by
  rw [IsFinMatroid]
  apply indep
  intro Y X hY hX hcard
  by_cases hXY : X \ Y = ∅
  · have := sdiff_eq_empty_iff_subset.mp hXY
    obtain ⟨x, hx⟩ := exists_eq_insert_of_card_succ this hcard
    use x
    refine ⟨hx.left, hx.right.left, ?_⟩
    rwa [← hx.right.right]
  · have hXY₁ : #(X \ Y) < #(Y \ X) := by
      rw [card_sdiff_lt_card_sdiff_iff]; simp [hcard]
    have hXY₂ : 0 < #(X \ Y) := by simp; exact nonempty_of_ne_empty hXY
    set u : ℕ := #(X \ Y) + #(Y \ X) with hu
    have hu' : 0 < u := by grind
    set v : ℕ := 2 * #(X \ Y) with hv
    have huv : v < u := by
      simp [u, v]
      rw [Nat.two_mul, add_lt_add_iff_left]
      exact card_sdiff_lt_card_sdiff_iff.mpr (by simp [hcard])
    set c : α → ℕ := fun x ↦ if x ∈ X then u else (if x ∈ Y then v else 0)
    have hw : weight c X < weight c Y := by
      simp [weight, c]
      rw [sum_ite_of_true (by simp)]
      nth_rw 1 [← sdiff_union_inter Y X]
      rw [sum_union (disjoint_sdiff_inter Y X)]
      rw [sum_ite_of_false (by simp), sum_ite_of_true (by grind)]
      rw [sum_ite_of_true (by simp)]
      simp
      nth_rw 1 [← sdiff_union_inter X Y, card_union_of_disjoint (disjoint_sdiff_inter X Y)]
      rw [add_mul, inter_comm, add_lt_add_iff_right]
      simp [u, v]
      calc #(X \ Y) * (#(X \ Y) + #(Y \ X))
      _ < #(X \ Y) * #(Y \ X) + #(X \ Y) * #(Y \ X) := by
        rwa [mul_add, add_lt_add_iff_right, mul_lt_mul_iff_right₀ hXY₂]
      _ = #(Y \ X) * (2 * #(X \ Y)) := by rw [two_mul, mul_comm, mul_add]
    by_contra hc
    simp at hc
    set xs := F.E.toList.mergeSort (fun x y ↦ decide (weightRel c x y)) with hxs
    have hxs' : xs.Pairwise (weightRel c) := by simp [hxs, pairwise_mergeSort']
    -- have (n m : ℕ) (hn : n < xs.length) (hm : m < xs.length) :
    --     xs[n] ∈ X → xs[m] ∈ Y \ X → m < n := by
    --   intro hnX hmY
    --   have := List.
    have hpart : ∃ l₁ l₂ l₃, l₁ ~ (F.E \ (X ∪ Y)).toList ∧ l₂ ~ Y.toList ∧ l₃ ~ X.toList ∧
        l₁ ++ l₂ ++ l₃ = xs := by
      sorry
    obtain ⟨l₁, l₂, l₃, hl₁, hl₂, hl₃, hlxs⟩ := hpart
    have hl₃' : ∀ l, l <+ l₃ → List.Greedy.select F.Indep l = l := by
      intro l hl
      induction l with
      | nil => simp
      | cons y ys ih =>
        rw [List.Greedy.select_cons_pos, cons_inj_right]
        exact ih (sublist_of_cons_sublist hl)
        refine F.indep_subset hX ?_
        rw [← toFinset_cons]
        intro z hz
        rw [mem_toFinset, ih (sublist_of_cons_sublist hl)] at hz
        rw [← mem_toList, Perm.mem_iff hl₃.symm]
        grind
    have hl₂' : ∀ x ∈ Y \ X, x ∉ List.Greedy.select F.Indep xs := by
      by_contra hc'
      simp at hc'
      obtain ⟨x, hx₁, hx₂, hx₃⟩ := hc'
      obtain ⟨n, hn₁, hn₂⟩ := mem_iff_getElem.mp (Sublist.mem hx₃ List.Greedy.select_sublist)
      rw [← hn₂, List.Greedy.select_iff hn₁] at hx₃
      refine hc x hx₁ hx₂ (F.indep_subset hx₃ ?_ (Y := insert x X))
      rw [hn₂, insert_subset_insert_iff hx₂]
      intro y hy
      rw [mem_toFinset]
      apply Sublist.mem ((Perm.mem_iff hl₃).mpr (mem_toList.mpr hy))
      have hl₃'' : l₃ = (xs.rtake (xs.length - n - 1)).rtake (l₃.length) := by
        rw [rtake.eq_1, rtake.eq_1, drop_drop]
        simp
        rw [show xs.length - (xs.length - n - 1) = n + 1 by omega]
        have : n + 1 ≤ (l₁ ++ l₂).length := by
          by_contra hc''
          rw [getElem_eq_iff hn₁, ← hlxs] at hn₂
          rw [getElem?_append_right (by grind)] at hn₂
          have : x ∈ l₃ := by grind
          exact hx₂ (mem_toList.mp ((Perm.mem_iff hl₃).mp this))
        have : xs.length = (l₁ ++ l₂).length + l₃.length := by grind
        rw [show (n + 1 + (xs.length - (n + 1) - l₃.length)) = xs.length - l₃.length by omega]
        rw [← hlxs, drop_left' (by rw [← hlxs] at this; omega)]
      have := hl₃' l₃ (by simp)
      rw [← this, hl₃'']
      apply List.Greedy.select_sublist' (P := F.Indep)
      rw [hxs]
      apply Nodup.mergeSort
      exact nodup_toList F.E
    set B := (Greedy.select F.Indep xs).toFinset with hB
    have hB₁ : X ⊆ B := by
      intro y hy
      have hy := (Perm.mem_iff hl₃).mpr (mem_toList.mpr hy)
      sorry
    have hB₁ : (B \ X) ∩ Y = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_inter, mem_sdiff] at hy
      have := hc y hy.right hy.left.right
      refine this (F.indep_subset (X := B) ?_ ?_)
      · sorry
      · grind
    have hcxs : weight c B = weight c X := by
      simp [weight, c]
      rw [← sdiff_union_inter B X, sum_union (by exact disjoint_sdiff_inter B X)]
      rw [show B ∩ X = X by grind, add_eq_right]
      rw [← sdiff_union_inter (B \ X) Y, sum_union (by exact disjoint_sdiff_inter (B \X) Y)]
      rw [hB₁, sum_empty]
      rw [sum_ite_of_false (by grind), sum_ite_of_false (by grind)]
      simp
    have := h c
      -- have : l₃ <+ (xs.rtake (xs.length - n - 1)) := by
      --   rw [rtake.eq_1, show (xs.length - (xs.length - n - 1)) = n + 1 by omega, ← hlxs]
      --   rw [drop_append_of_le_length ?_]
      --   · apply sublist_append_right
      --   by_contra hc''
      --   rw [getElem_eq_iff hn₁, ← hlxs] at hn₂
      --   rw [getElem?_append_right (by grind)] at hn₂
      --   have : x ∈ l₃ := by grind
      --   exact hx₂ (mem_toList.mp ((Perm.mem_iff hl₃).mp this))



    -- have hw' : weight c X = weight c (Greedy_set F c) := by



  -- have hX₁ : ∀ u v : ℝ, weight (c u v) X = X.card * u := by
  --   intro u v
  --   simp [weight, c]
  --   rw [Finset.sum_ite_of_true (by simp)]
  --   simp
  -- have hY₁ : ∀ u v : ℝ, weight (c u v) Y = (X ∩ Y).card * u + (Y.card - (X ∩ Y).card) * v := by
  --   intro u v
  --   simp [weight, c]
  --   nth_rw 1 [← Finset.sdiff_union_inter Y X]
  --   rw [Finset.sum_union (by exact Finset.disjoint_sdiff_inter Y X)]
  --   rw [Finset.sum_ite_of_false (by simp), Finset.sum_ite_of_true (by grind)]
  --   rw [Finset.sum_ite_of_true (by simp)]
  --   rw [Finset.inter_comm Y X, add_comm]
  --   simp [Finset.card_sdiff]
  --   rw [Nat.cast_sub (by apply Finset.card_le_card; simp)]
  --   simp
  -- have : ∃ u v : ℝ, u > v ∧ v > 0 ∧ weight (c u v) X < weight (c u v) Y := by
  --   simp [weight, c]




theorem Matroid_iff_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
  IsFinMatroid F ↔
  ∀ c : α → ℝ,
      Maximal F.Indep (Greedy_set F c) ∧
      weight_is_maximum F c (Greedy_set F c) := by
  sorry

end FinMatroid
