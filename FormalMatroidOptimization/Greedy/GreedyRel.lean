import FormalMatroidOptimization.Greedy.Basic

-- class TotalPreorder (α : Type u) extends LE α where
--   le_refl : ∀ a : α, a ≤ a
--   le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
--   le_total : ∀ a b : α, a ≤ b ∨ b ≤ a

namespace GreedyRel

-- def bla (β : Type*) [h : TotalPreorder β] := h.le

-- def select' {α β : Type*} [DecidableEq α] [hβ : TotalPreorder β] [DecidableRel hβ.le]
--     (P : Finset α → Bool) (lst : List α) (c : α → β) :
--     List α := Greedy.select P (lst.mergeSort (fun x y ↦ c x ≤ c y))

-- def select {α β : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
--     (c : α → β) (r : β → β → Prop) [DecidableRel r] [IsTotal β r] [IsTrans β r] :
--     List α := Greedy.select P (lst.mergeSort (fun x y ↦ r (c x) (c y)))

-- theorem pairwise {α β : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) (c : α → β)
--     (r : β → β → Prop) [DecidableRel r] [IsTotal β r] [IsTrans β r] :
--     List.Pairwise r ((select P lst c r).map c) := by
--   let s (x y : α) : Prop := r (c x) (c y)
--   let hs (x y : α) : s x y = r (c x) (c y) := by rfl
--   have H : ∀ x y, s x y → r (c x) (c y) := by intro x y hs; unfold s at hs; assumption
--   apply List.Pairwise.map c H
--   unfold select
--   refine List.Pairwise.sublist Greedy.select_sublist ?_
--   have : (fun x y ↦ decide (s x y)) = (fun x y ↦ decide (r (c x) (c y))) := by ext x y; simp [hs]
--   rw [← this]
--   apply @List.pairwise_mergeSort' α s (Order.Preimage.decidable c r) (Order.Preimage.instIsTotal)
--     (Order.Preimage.instIsTrans)

def select {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List α := Greedy.select P (lst.mergeSort (fun x y ↦ r x y))

noncomputable def select_cost {α β : Type*} [hα : DecidableEq α] [LinearOrder β]
    (P : Finset α → Bool) (lst : List α) (c : α → β) :
    List α := @select α hα P lst (fun x y ↦ c x ≤ c y) (Classical.decRel (fun x y ↦ c x ≤ c y))
    (Order.Preimage.instIsTotal) (Order.Preimage.instIsTrans)

theorem pairwise {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List.Pairwise r (select P lst r) := by
  unfold select
  refine List.Pairwise.sublist Greedy.select_sublist ?_
  exact List.pairwise_mergeSort' r lst

theorem pairwise_cost {α β : Type*} [hα : DecidableEq α] [LinearOrder β] (P : Finset α → Bool)
    (lst : List α) (c : α → β) :
    List.Pairwise (· ≤ ·) ((select_cost P lst c).map c) := by
  apply @List.Pairwise.map β α (fun x y ↦ c x ≤ c y)
  · simp
  · unfold select_cost
    apply @pairwise α hα P lst (fun x y ↦ c x ≤ c y) (Classical.decRel (fun x y ↦ c x ≤ c y))
      (Order.Preimage.instIsTotal) (Order.Preimage.instIsTrans)

end GreedyRel
