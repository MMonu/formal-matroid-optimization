import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Sublists

import FormalMatroidOptimization.List.Rtake
import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.List.MaxRel

/-!
# Greedy selection of elements in a list

## Implemenation Details

Due to the implemenation of lists in Lean, the elements are considered from right to left.

## Main Definitions

* `List.Greedy.select P l` Greedy select elements of the list `l` from right to left, based on the
  predicate `P`.

* `List.Greedy.select_iff` Charcterize exactly when an element is selected, based on the predicate
  during the greedy selection algorithm.

* `List.Greedy.selectRel P r l` Sort the list `l` with respect to the relation `r` using mergeSort,
  before the greedy selection.
-/

namespace List

theorem mergeSort_toFinset_eq {α : Type*} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
    (l.mergeSort (fun a b ↦ r a b)).toFinset = l.toFinset := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := mergeSort_cons (le := fun a b ↦ decide (r a b))
      (by simp only [decide_eq_true_eq]; intro a b c hab hbc; exact trans_of r hab hbc)
      (by simp [IsTotal.total (r := r)]) x xs
    simp [h1]
    congr
    rwa [h2, toFinset_append] at ih

theorem mergeSort_cons_min {α : Type*} [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
    [IsTotal α r] [IsTrans α r] {x : α} {xs : List α} (h : ∀ y ∈ xs, r x y ∧ ¬r y x) :
    (x :: xs).mergeSort (fun a b ↦ r a b) = x :: xs.mergeSort (fun a b ↦ r a b) := by
  obtain ⟨l₁, l₂, h1, h2, h3⟩ := mergeSort_cons (le := fun a b ↦ decide (r a b))
    (by simp only [decide_eq_true_eq]; intro a b c hab hbc; exact trans_of r hab hbc)
    (by simp [IsTotal.total (r := r)]) x xs
  have hl₁: l₁ = [] := by
    by_contra hc
    obtain ⟨y, hy⟩ := exists_mem_of_ne_nil l₁ hc
    have : y ∈ (l₁ ++ l₂).toFinset := by simp [hy]
    rw [← h2, mergeSort_toFinset_eq, mem_toFinset] at this
    have hpos := (h y this).left
    have hneg := (h3 y hy)
    aesop
  simp [hl₁] at h1 h2
  simp [h1, h2]

theorem mergeSort_cons_max {α : Type*} [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
    [IsTotal α r] [IsTrans α r] {x : α} {xs : List α} (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    (x :: xs).mergeSort (fun a b ↦ r a b) = xs.mergeSort (fun a b ↦ r a b) ++ [x] := by
  obtain ⟨l₁, l₂, h1, h2, h3⟩ := mergeSort_cons (le := fun a b ↦ decide (r a b))
      (by simp only [decide_eq_true_eq]; intro a b c hab hbc; exact trans_of r hab hbc)
      (by simp [IsTotal.total (r := r)]) x xs
  have hp := pairwise_mergeSort' r (x :: xs)
  rw [h1] at hp
  have hl₂ : l₂ = [] := by
    by_contra hc
    obtain ⟨y, hy⟩ := exists_mem_of_ne_nil l₂ hc
    have : y ∈ (l₁ ++ l₂).toFinset := by simp [hy]
    rw [← h2, mergeSort_toFinset_eq, mem_toFinset] at this
    have hpos := (h y this).left
    have hneg := Pairwise.rel_head_tail (Pairwise.sublist (sublist_append_right l₁ (x :: l₂)) hp) hy
    aesop
  simp [hl₂] at h1 h2
  simp [h1, h2]

theorem mergeSort_unique_of_antisymm {α : Type*}
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l₁ l₂ : List α} (ha : ∀ x y, x ∈ l₁ → y ∈ l₁ → r x y ∧ r y x → x = y) :
    l₂ ~ l₁ → Pairwise r l₂ → l₂ = l₁.mergeSort (fun a b ↦ r a b) := by
  intro hy₁ hy₂
  have hy₁ := Trans.simple hy₁ (l₁.mergeSort_perm (fun a b ↦ r a b)).symm
  refine Perm.eq_of_pairwise (by grind) hy₂ (pairwise_mergeSort' r l₁) (by grind)

theorem mergeSort_max_of_antisymm {α : Type*} [DecidableEq α]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l₁ : List α} (hl₁ : l₁ ≠ []) (ha : ∀ x y, x ∈ l₁ → y ∈ l₁ → r x y ∧ r y x → x = y) :
    l₁.mergeSort (fun a b ↦ r a b) =
    (l₁.erase (l₁.maxRel r hl₁)).mergeSort (fun a b ↦ r a b) ++ [l₁.maxRel r hl₁] := by
  refine (mergeSort_unique_of_antisymm ha ?_ ?_).symm
  · have h := Trans.simple (perm_cons_erase (l₁.maxRel_mem r hl₁)) (perm_append_singleton _ _).symm
    exact (Trans.simple h (Perm.append_right _ (mergeSort_perm _ (fun a b ↦ r a b))).symm).symm
  · refine pairwise_append.mpr ⟨pairwise_mergeSort' r _, pairwise_singleton r _, ?_⟩
    intro x hx y hy
    rw [mem_singleton] at hy
    have := maxRel_nle r hl₁ x (by grind [mem_mergeSort])
    rw [← hy] at this
    cases total_of r x y with
    | inl h' => exact h'
    | inr h' => exact this h'

namespace Greedy

variable {α : Type*} [DecidableEq α]

/-- Greedily select elements from a list, right to left -/
def select {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P] : (l : List α) →
  List α
  | [] => []
  | x :: xs =>
    if P (insert x (select P xs).toFinset) then
      x :: (select P xs)
    else
      select P xs

namespace GreedySelectExample

def P : Finset (Fin 3) → Bool := fun X ↦ match X.card with
| 0 => true
| 1 => true
| 2 => true
| _ => false

def P' : Finset (Fin 3) → Prop := fun X ↦ P (X) = true
instance hP' : DecidablePred P' := by intro y; rw [P']; infer_instance

def xs : List (Fin 3) := [3, 2, 1]

#eval select P' xs

end GreedySelectExample

@[simp]
theorem select_nil {P : Finset α → Prop} [DecidablePred P] :
    select P [] = [] := by
  simp [select]

@[simp]
theorem select_cons_pos {P : Finset α → Prop} [DecidablePred P] {x : α} {xs : List α}
    (hP : P (insert x (select P xs).toFinset)) : select P (x :: xs) = x :: (select P xs) := by
  simp [select, hP]

@[simp]
theorem select_cons_neg {P : Finset α → Prop} [DecidablePred P] {x : α} {xs : List α}
    (hP : ¬(P (insert x (select P xs).toFinset))) : select P (x :: xs) = select P xs := by
  simp [select, hP]

theorem select_sublist {P : Finset α → Prop} [DecidablePred P] {l : List α} :
  select P l <+ l := by
  induction l with
  | nil => simp [select]
  | cons x xs ih =>
    simp only [select]
    by_cases hP : P (insert x (select P xs).toFinset) <;> simp [hP, ih]

theorem select_sublist_succ {P : Finset α → Prop} [DecidablePred P] {l : List α} {n : ℕ} :
    select P (l.rtake n) <+ select P (l.rtake (n + 1)) := by
  by_cases hn : n < l.length
  · simp only [rtake_eq_getElem_cons' hn, select]
    by_cases hP : P (insert l[l.length - 1 - n] (select P (l.rtake n)).toFinset) <;> simp [hP]
  · simp [rtake.eq_1, show l.length - n = l.length - (n + 1) by omega]

theorem select_monotone {P : Finset α → Prop} [DecidablePred P] {l : List α} {n m : ℕ}
    (hmn : m ≤ n) : select P (l.rtake m) <+ select P (l.rtake n) := by
  induction n with
  | zero => simp [nonpos_iff_eq_zero.mp hmn]
  | succ n ih =>
    by_cases hmn' : m = n + 1
    · simp [hmn']
    · exact Sublist.trans (ih (by omega)) (select_sublist_succ)

theorem select_sublist' {P : Finset α → Prop} [DecidablePred P] {l : List α} (n : ℕ) :
    select P (l.rtake n) <+ select P l := by
  by_cases hn : n ≤ l.length
  · exact Sublist.trans (select_monotone hn) (by rw [rtake_length])
  · rw [rtake_of_length_le (le_of_lt (Nat.not_le.mp hn))]

theorem select_monotone' {P : Finset α → Prop} [DecidablePred P] (l₁ l₂ : List α) :
    select P l₂ <+ select P (l₁ ++ l₂) := by
  nth_rw 1 [← rtake_right' (show l₂.length = l₂.length by rfl)]
  refine select_sublist' l₂.length

theorem select_sublist_cons {P : Finset α → Prop} [DecidablePred P] {l : List α} (h : l ≠ []) :
    select P l <+ l.head h :: select P l.tail := by
  nth_rw 1 [← cons_head_tail h, select.eq_2]
  by_cases hP : P (insert (l.head h) (select P l.tail).toFinset) <;> simp [hP]

theorem select_sublist_append {P : Finset α → Prop} [DecidablePred P] {l : List α} (n : ℕ) :
    select P l <+ l.take (l.length - n) ++ select P (l.rtake n) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hn : xs.length < n
    · simp [rtake.eq_1, tsub_eq_zero_of_le (Nat.succ_le_of_lt hn)]
    · have : xs.length - n = xs.length + 1 - n - 1 := by omega
      calc select P (x :: xs)
      _ <+ x :: select P xs := by apply select_sublist_cons; simp
      _ <+ x :: take (xs.length - n) xs ++ select P (xs.rtake n) := by simp [ih]
      _ =  take ((x :: xs).length - n) (x :: xs) ++ select P (xs.rtake n) := by
        congr; rw [length_cons, take_cons <| by omega, this]
      _ <+ take ((x :: xs).length - n) (x :: xs) ++ select P ((x :: xs).rtake n) := by
        gcongr; simp [rtake.eq_1, drop_cons (by exact tsub_pos_iff_not_le.mpr hn), this]

theorem select_append_sublist {P : Finset α → Prop} [DecidablePred P] {l₁ l₂ : List α} :
    select P (l₁ ++ l₂) <+ l₁ ++ select P l₂ := by
  nth_rw 2 [← rtake_right' (show l₂.length = l₂.length by rfl)]
  · nth_rw 2 [← take_left' (show l₁.length = (l₁ ++ l₂).length - l₂.length by simp)]
    refine select_sublist_append (P := P) _

theorem select_mem_of_P {P : Finset α → Prop} [DecidablePred P] {l : List α} {n : ℕ}
    (hn : n < l.length)
    (hP : P (insert l[n] (select P (l.rtake (l.length - n - 1))).toFinset)) :
    l[n] ∈ select P l := by
  apply Sublist.mem ?_ (select_sublist' (l.length - n - 1 + 1))
  have : l.length - 1 - (l.length - n - 1) = n := by omega
  rw [rtake_eq_getElem_cons' <| by omega, select.eq_2, if_pos ?_]
  · simp [this]
  · simp [this, hP]

theorem select_of_not_mem {P : Finset α → Prop} [DecidablePred P] {x : α} {l : List α} {n : ℕ}
    (h : x ∉ select P l) : x ∉ select P (l.rtake n) := by
  by_contra hc
  grind [select_sublist']

theorem select_ex_P_of_mem {P : Finset α → Prop} [DecidablePred P] {l : List α} {x : α}
    (h : x ∈ select P l) :
    ∃ n : ℕ, ∃ hn : n < l.length, x = l[n] ∧
    P (insert l[n] (select P (l.rtake (l.length - n - 1))).toFinset) := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have : ∀ m : ℕ, m ≤ l.length → x ∉ select P (l.rtake m) := by
    intro m hm; induction m with
    | zero => simp
    | succ m ih =>
      rw [rtake_eq_getElem_cons' (by omega), select.eq_2]
      by_cases hmx : x = l[l.length - 1 - m]
      · have := hc (l.length - 1 - m) (by omega) hmx
        rw [show l.length - (l.length - 1 - m) - 1 = m by omega] at this
        rw [if_neg (by simp[this])]
        exact (ih (Nat.le_of_succ_le hm))
      · by_cases hP : P (insert l[l.length - 1 - m] (select P (l.rtake m)).toFinset)
        <;> simp [hP, hmx, ih (Nat.le_of_succ_le hm)]
  specialize this l.length (by omega)
  rw [rtake_length] at this
  contradiction

theorem select_iff {P : Finset α → Prop} [DecidablePred P] {l : List α}
    {hl : Nodup l} {n : ℕ} (hn : n < l.length) :
    l[n] ∈ select P l ↔ P (insert l[n] (select P (l.rtake (l.length - n - 1))).toFinset)
    := by
  constructor
  · intro h
    obtain ⟨m, hm1, hm2, hm3⟩ := select_ex_P_of_mem h
    have := (Nodup.getElem_inj_iff hl).mp hm2
    simpa [this]
  · intro h
    exact select_mem_of_P hn h

theorem select_last {P : Finset α → Prop} [DecidablePred P] {x : α} {l : List α} :
    if P {x} then
      select P (l ++ [x]) = (select (fun s ↦ P (s ∪ {x})) l) ++ [x]
    else
      select P (l ++ [x]) = select P l
    := by
  induction l with
  | nil => simp [select]
  | cons y ys ih =>
    by_cases hP₁ : P {x}
    · simp only [hP₁, ↓reduceIte, Finset.union_singleton, cons_append] at ih ⊢
      have h := calc (insert x (insert y (select (fun s ↦ P (insert x s)) ys).toFinset))
        _ = (insert y (select (fun s ↦ P (insert x s)) ys ++ [x]).toFinset) := by
          grind [toFinset_append, toFinset_cons, toFinset_nil, insert_empty_eq x]
        _ = (insert y (select P (ys ++ [x])).toFinset) := by simp [ih]
      by_cases hP₂ : P (insert y (select P (ys ++ [x])).toFinset)
      · rw [select_cons_pos hP₂, ih, select_cons_pos (by simp [h, hP₂])]
        simp
      · rw [select_cons_neg hP₂, ih, select_cons_neg (by simp [h, hP₂])]
    · simp only [hP₁, ↓reduceIte, cons_append] at ih ⊢
      have h := calc (insert y (select P (ys ++ [x])).toFinset)
        _ = (insert y (select P ys).toFinset) := by simp [ih]
      by_cases hP₂ : P (insert y (select P (ys ++ [x])).toFinset)
      · rw [select_cons_pos hP₂, ih, select_cons_pos (by grind)]
      · rw [select_cons_neg hP₂, ih, select_cons_neg (by grind)]

def selectRel (P : Finset α → Prop) [DecidablePred P] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l : List α) :
    List α := Greedy.select P (l.mergeSort (fun x y ↦ r x y))

@[simp] theorem selectRel_nil (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] : selectRel P r [] = [] := by
  simp [selectRel]

theorem selectRel_cons_min (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {x : α} {l : List α}
    (h : ∀ y ∈ l, r x y ∧ ¬r y x) :
    if P (insert x (selectRel P r l).toFinset) then
      selectRel P r (x :: l) = x :: selectRel P r l
    else
      selectRel P r (x :: l) = selectRel P r l
    := by
  simp [selectRel, mergeSort_cons_min h, Greedy.select]

theorem selectRel_cons_max {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {l : List α} (h : ∀ y ∈ l, r y x ∧ ¬r x y) :
    if P {x} then
      selectRel P r (x :: l) = selectRel (fun s ↦ P (s ∪ {x})) r l ++ [x]
    else
      selectRel P r (x :: l) = selectRel P r l
    := by
  grind [selectRel, mergeSort_cons_max, select_last]

theorem selectRel_pairwise (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
    Pairwise r (selectRel P r l) := by
  unfold selectRel
  refine Pairwise.sublist select_sublist ?_
  exact pairwise_mergeSort' r l

theorem selectRel_max_of_antisymm
    {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l : List α} (hl₁ : l ≠ []) (hl₂ : l.Nodup)
    (ha : ∀ x y, x ∈ l → y ∈ l → r x y ∧ r y x → x = y) :
    let x := l.maxRel r hl₁
    if P {x} then
      selectRel P r l = selectRel (fun s ↦ P (s ∪ {x})) r (l.erase x) ++ [x]
    else
      selectRel P r l = selectRel P r (l.erase x)
    := by
  set x := l.maxRel r hl₁ with hx
  have h := calc  (x :: (l.erase x)).mergeSort (fun a b ↦ r a b)
    _ ~ x :: (l.erase x) := mergeSort_perm (x :: l.erase x) fun a b ↦ decide (r a b)
    _ ~ l                := (perm_cons_erase (l.maxRel_mem r hl₁)).symm
  simp only [selectRel]
  rw [← mergeSort_unique_of_antisymm ha h (pairwise_mergeSort' r _)]
  simp only [← selectRel.eq_1]
  refine selectRel_cons_max ?_
  intro y hy
  have hy' : x ≠ y := by by_contra hc; rw [hc] at hy; exact (Nodup.not_mem_erase hl₂) hy
  have h₀ := ha x y (maxRel_mem r hl₁) (mem_of_mem_erase hy)
  have h₁ := maxRel_nle r hl₁ y (mem_of_mem_erase hy)
  rw [← hx] at h₁
  cases total_of r x y with
  | inl h₂ => grind
  | inr h₂ => grind

end Greedy

end List
