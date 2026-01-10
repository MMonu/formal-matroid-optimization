import FormalMatroidOptimization.Greedy.Basic
import FormalMatroidOptimization.List.MinRel

namespace GreedyRel

def select {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List α := Greedy.select P (lst.mergeSort (fun x y ↦ r x y))

theorem select_pairwise {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List.Pairwise r (select P lst r) := by
  unfold select
  refine List.Pairwise.sublist Greedy.select_sublist ?_
  exact List.pairwise_mergeSort' r lst

def select'_internal {α : Type*} [DecidableEq α] (P : Finset α → Bool) (s indep : List α)
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] : List α :=
  let sP := s.filter (fun x ↦ P (insert x indep.toFinset))
  if hsP : sP ≠ [] then
    let y := sP.min_rel r hsP
    select'_internal P (s.erase y) (y :: indep) r
  else
    indep
  termination_by
    s.length
  decreasing_by
    apply Order.lt_of_succ_lt_succ
    rw [Order.succ_eq_add_one, List.length_erase_add_one ?_]
    · simp
    · have : (List.filter (fun x ↦ P (insert (↑x) indep.toFinset)) s.attach).unattach ⊆ s := by simp
      exact this (List.min_rel_mem r hsP)

def select' {α : Type*} [DecidableEq α] (P : Finset α → Bool) (s : List α) (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] : List α :=
  select'_internal P s ∅ r

-- noncomputable def select_cost {α β : Type*} [hα : DecidableEq α] [LinearOrder β]
--     (P : Finset α → Bool) (lst : List α) (c : α → β) :
--     List α := @select α hα P lst (fun x y ↦ c x ≤ c y) (Classical.decRel (fun x y ↦ c x ≤ c y))
--     (Order.Preimage.instIsTotal) (Order.Preimage.instIsTrans)

-- theorem select_pairwise_cost {α β : Type*} [hα : DecidableEq α] [LinearOrder β] (P : Finset α → Bool)
--     (lst : List α) (c : α → β) :
--     List.Pairwise (· ≤ ·) ((select_cost P lst c).map c) := by
--   apply @List.Pairwise.map β α (fun x y ↦ c x ≤ c y)
--   · simp
--   · unfold select_cost
--     apply @pairwise α hα P lst (fun x y ↦ c x ≤ c y) (Classical.decRel (fun x y ↦ c x ≤ c y))
--       (Order.Preimage.instIsTotal) (Order.Preimage.instIsTrans)

end GreedyRel
