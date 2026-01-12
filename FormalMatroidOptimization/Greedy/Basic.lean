import Mathlib.Tactic

import FormalMatroidOptimization.List.MaxRel
import FormalMatroidOptimization.FinMatroid.Basic

open List

namespace Greedy

def selectRel_internal {α : Type*} [DecidableEq α] (P : Finset α → Bool) (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] (s indep : List α) : List α :=
  let sP := s.filter (fun x ↦ P (insert x indep.toFinset))
  if hsP : sP ≠ [] then
    let y := sP.maxRel r hsP
    selectRel_internal P r (s.erase y) (y :: indep)
  else
    indep
  termination_by
    s.length
  decreasing_by
    apply Order.lt_of_succ_lt_succ
    rw [Order.succ_eq_add_one, List.length_erase_add_one ?_]
    · simp
    · have : (filter (fun x ↦ P (insert (↑x) indep.toFinset)) s.attach).unattach ⊆ s := by simp
      exact this (maxRel_mem r hsP)

def selectRel {α : Type*} [DecidableEq α] (P : Finset α → Bool) (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (lst : List α) : List α :=
  selectRel_internal P r lst ∅

@[simp] theorem selectRel_nil {α : Type*} [DecidableEq α] (P : Finset α → Bool) (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] : selectRel P r [] = [] := by
  simp [selectRel, selectRel_internal]

theorem selectRel_internal_subset {α : Type*} [DecidableEq α] (P : Finset α → Prop)
    [DecidablePred P] (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs : List α}
    {ys : List α} :
    ys ⊆ selectRel_internal P r xs ys := by
  match xs with
  | [] =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) [] with hsP₁
    rw [dif_neg (by simp [hsP₁])]
    simp
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      exact subset_of_cons_subset (selectRel_internal_subset P r
        (xs := ((x :: xs).erase (List.maxRel r sP hsP₂))) (ys := ((List.maxRel r sP hsP₂) :: ys)))
    · rw [dif_neg hsP₂]
      simp
  termination_by
    xs.length
  decreasing_by
    grind [List.maxRel_mem]

theorem selectRel_internal_indep {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs : List α} {ys : List α}
    (hys : P ys.toFinset) : P (selectRel_internal P r xs ys).toFinset := by
    match xs with
  | [] =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) [] with hsP₁
    rwa [dif_neg (by simp [hsP₁])]
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      apply (selectRel_internal_indep P r
        (xs := ((x :: xs).erase (List.maxRel r sP hsP₂))) (ys := ((List.maxRel r sP hsP₂) :: ys)))
      have := (mem_filter.mp (maxRel_mem r hsP₂)).right
      rw [Bool.decide_iff] at this
      simpa
    · rwa [dif_neg hsP₂]
  termination_by
    xs.length
  decreasing_by
    grind [List.maxRel_mem]

theorem selectRel_internal_with_max {α : Type*} [DecidableEq α] (P : Finset α → Prop)
    [DecidablePred P] (hP : IndepSystem.HereditaryProperty P) (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] {x : α} {xs : List α} {ys : List α}
    (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    if P (insert x ys.toFinset) then
      selectRel_internal P r (x :: xs) ys = selectRel_internal P r xs (x :: ys)
    else
      selectRel_internal P r (x :: xs) ys = (selectRel_internal P r xs ys)
    := by
  rw [selectRel_internal]
  set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) (x :: xs) with hsP₁
  by_cases hx : x ∈ sP
  · have hP₁ := (Bool.decide_iff _).mp (List.mem_filter.mp hx).right
    rw [if_pos hP₁]
    have hxsP : x ∈ sP := by simp [hsP₁, hP₁]
    have hsP₂ : sP ≠ [] := by by_contra; apply List.not_mem_nil; rwa [this] at hxsP
    rw [dif_pos hsP₂]
    have : ∀ y ∈ filter (fun x ↦ decide (P (insert x ys.toFinset))) xs, r y x ∧ ¬r x y := by grind
    have : List.maxRel r sP hsP₂ = x := by rw [← (maxRel_with_max r this)]; grind
    grind
  · have hP₁ : ¬P (insert x ys.toFinset) := by grind
    rw [filter_cons_of_neg (by simp [hP₁])] at hsP₁
    rw [if_neg hP₁, selectRel_internal, ← hsP₁]
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂, dif_pos hsP₂]
      set y := List.maxRel r sP hsP₂ with hy₁
      have : (x :: xs).erase y = x :: xs.erase y := by
        rw [erase_cons_tail ?_]
        have := Finset.forall_mem_not_eq.mpr ((not_iff_not.mpr (List.mem_toFinset)).mpr hx)
        simp [hy₁, (this (List.maxRel r sP hsP₂) (by simp [maxRel_mem r hsP₂]))]
      have  h' := selectRel_internal_with_max P hP r ?_ (x := x) (xs := xs.erase y) (ys := y :: ys)
      · by_cases hP₂ : P (insert x (y :: ys).toFinset)
        · have : (insert x ys.toFinset) ⊆ (insert x (y :: ys).toFinset) := by simp
          exact False.elim (hP₁ (hP hP₂ this))
        · grind
      · grind
    · grind
  termination_by
    xs.length
  decreasing_by
    grind [List.maxRel_mem]

end Greedy
