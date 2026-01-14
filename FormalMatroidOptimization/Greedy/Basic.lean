import Mathlib.Tactic

import FormalMatroidOptimization.List.MaxRel
import FormalMatroidOptimization.FinMatroid.Basic

open List

namespace Greedy

variable {α : Type*} [DecidableEq α]

def selectRel_internal (P : Finset α → Prop) [DecidablePred P] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (xs ys : List α) : List α :=
  let sP := xs.filter (fun x ↦ P (insert x ys.toFinset))
  if hsP : sP ≠ [] then
    let y := sP.maxRel r hsP
    selectRel_internal P r (xs.erase y) (y :: ys)
  else
    ys
  termination_by
    xs.length
  decreasing_by
    apply Order.lt_of_succ_lt_succ
    rw [Order.succ_eq_add_one, List.length_erase_add_one ?_]
    · simp
    · have : (filter (fun x ↦ P (insert (↑x) ys.toFinset)) xs.attach).unattach ⊆ xs := by
        intro z hz; simp at hz; exact hz.left
      exact this (maxRel_mem r hsP)

def selectRel (P : Finset α → Prop) [DecidablePred P] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (xs : List α) : List α :=
  selectRel_internal P r xs []

@[simp] theorem selectRel_nil {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] : selectRel P r [] = [] := by
  simp [selectRel, selectRel_internal]


theorem selectRel_internal_subset {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs ys : List α} :
    ys ⊆ selectRel_internal P r xs ys := by
  match xs with
  | [] =>
    grind [selectRel_internal]
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      exact subset_of_cons_subset (selectRel_internal_subset
        (xs := ((x :: xs).erase (List.maxRel r sP hsP₂))) (ys := ((List.maxRel r sP hsP₂) :: ys)))
    · rw [dif_neg hsP₂]
      simp
  termination_by
    xs.length
  decreasing_by
    grind [List.maxRel_mem]

theorem selectRel_internal_indep {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs ys : List α} (hys : P ys.toFinset) :
    P (selectRel_internal P r xs ys).toFinset := by
  match xs with
  | [] =>
    grind [selectRel_internal]
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      apply (selectRel_internal_indep
        (xs := ((x :: xs).erase (List.maxRel r sP hsP₂))) (ys := ((List.maxRel r sP hsP₂) :: ys)))
      have := (mem_filter.mp (maxRel_mem r hsP₂)).right
      rw [Bool.decide_iff] at this
      simpa
    · rwa [dif_neg hsP₂]
  termination_by
    xs.length
  decreasing_by
    grind [List.maxRel_mem]

theorem selectRel_internal_prop
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs ys : List α} :
    selectRel_internal P r xs ys = (selectRel_internal (fun s ↦ P (s ∪ ys.toFinset)) r xs []) ++ ys
    := by
  rw [selectRel_internal.eq_def, selectRel_internal.eq_def]
  set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) xs with hsP₁
  have : sP = filter (fun x ↦ decide (P (insert x [].toFinset ∪ ys.toFinset))) xs := by rfl
  rw [← this]
  by_cases hsP₂ : sP ≠ []
  · rw [dif_pos hsP₂, dif_pos hsP₂]
    have := selectRel_internal_prop (r := r) (xs := (xs.erase (List.maxRel r sP hsP₂)))
      (ys := (List.maxRel r sP hsP₂) :: ys) hP
    rw [this]
    set P₁ := fun s ↦ P (s ∪ ys.toFinset) with hP₁
    have hP₂ : IndepSystem.HereditaryProperty P₁ := by
      intro X Y hX hXY
      simp only [hP₁] at hX ⊢
      have : (Y ∪ ys.toFinset) ⊆ (X ∪ ys.toFinset) := by grind
      exact hP hX this
    have := selectRel_internal_prop (r := r) (xs := (xs.erase (List.maxRel r sP hsP₂)))
      (ys := [List.maxRel r sP hsP₂]) hP₂
    rw [this, ← singleton_append, append_assoc]
    congr
    ext x
    simp [hP₁]
  · rw [dif_neg hsP₂, dif_neg hsP₂]
    simp
  termination_by
    xs.length
  decreasing_by
    · grind [List.maxRel_mem]
    · grind [List.maxRel_mem]

theorem selectRel_internal_with_max
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs ys : List α} (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    if P (insert x ys.toFinset) then
      selectRel_internal P r (x :: xs) ys = selectRel_internal P r xs (x :: ys)
    else
      selectRel_internal P r (x :: xs) ys = selectRel_internal P r xs ys
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
      have  h' := selectRel_internal_with_max hP ?_
        (r := r) (x := x) (xs := xs.erase y) (ys := y :: ys)
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

theorem selectRel_with_max
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs : List α} (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    if P {x} then
      selectRel P r (x :: xs) = selectRel (fun s ↦ P (s ∪ {x})) r xs ++ [x]
    else
      selectRel P r (x :: xs) = selectRel P r xs
    := by
  unfold selectRel
  have := selectRel_internal_with_max hP h (ys := [])
  have h₁ : (insert x [].toFinset) = {x} := by rw [toFinset_nil, insert_empty_eq]
  rw [h₁] at this
  by_cases hP₁ : P {x}
  · rw [if_pos hP₁] at this ⊢
    simp [this, selectRel_internal_prop hP]
  · rwa [if_neg hP₁] at this ⊢

end Greedy
