import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

import FormalMatroidOptimization.List.Rtake
import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.List.MaxRel

namespace List

theorem mergeSort_toFinset_eq {α : Type*} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (xs : List α) :
    (xs.mergeSort (fun a b ↦ r a b)).toFinset = xs.toFinset := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons (le := fun a b ↦ decide (r a b))
      (by simp only [decide_eq_true_eq]; intro a b c hab hbc; exact trans_of r hab hbc)
      (by simp [IsTotal.total (r := r)]) x xs
    simp [h1]
    congr
    rwa [h2, toFinset_append] at ih

theorem mergeSort_cons_min {α : Type*} [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
    [IsTotal α r] [IsTrans α r] {x : α} {xs : List α} (h : ∀ y ∈ xs, r x y ∧ ¬r y x) :
    (x :: xs).mergeSort (fun a b ↦ r a b) = x :: xs.mergeSort (fun a b ↦ r a b) := by
  obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons (le := fun a b ↦ decide (r a b))
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
  obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons (le := fun a b ↦ decide (r a b))
      (by simp only [decide_eq_true_eq]; intro a b c hab hbc; exact trans_of r hab hbc)
      (by simp [IsTotal.total (r := r)]) x xs
  have hp := List.pairwise_mergeSort' r (x :: xs)
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
    {xs ys : List α} (ha : ∀ x y, x ∈ xs → y ∈ xs → r x y ∧ r y x → x = y) :
    ys ~ xs → Pairwise r ys → ys = xs.mergeSort (fun a b ↦ r a b) := by
  intro hy₁ hy₂
  have hy₁ := Trans.simple hy₁ (xs.mergeSort_perm (fun a b ↦ r a b)).symm
  refine Perm.eq_of_pairwise (by grind) hy₂ (pairwise_mergeSort' r xs) (by grind)

theorem mergeSort_max_of_antisymm {α : Type*} [DecidableEq α]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs : List α} (hxs : xs ≠ []) (ha : ∀ x y, x ∈ xs → y ∈ xs → r x y ∧ r y x → x = y) :
    xs.mergeSort (fun a b ↦ r a b) =
    (xs.erase (xs.maxRel r hxs)).mergeSort (fun a b ↦ r a b) ++ [xs.maxRel r hxs] := by
  refine (mergeSort_unique_of_antisymm ha ?_ ?_).symm
  · have h := Trans.simple (perm_cons_erase (xs.maxRel_mem r hxs)) (perm_append_singleton _ _).symm
    exact (Trans.simple h (Perm.append_right _ (mergeSort_perm _ (fun a b ↦ r a b))).symm).symm
  · refine pairwise_append.mpr ⟨pairwise_mergeSort' r _, pairwise_singleton r _, ?_⟩
    intro x hx y hy
    rw [mem_singleton] at hy
    have := maxRel_nle r hxs x (by grind [mem_mergeSort])
    rw [← hy] at this
    cases total_of r x y with
    | inl h' => exact h'
    | inr h' => exact this h'

namespace Greedy

variable {α : Type*} [DecidableEq α]

/-- Greedily select elements from a list, right to left -/
def select {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P] : (xs : List α) →
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

theorem select_sublist {P : Finset α → Prop} [DecidablePred P] {xs : List α} :
  select P xs <+ xs := by
  induction xs with
  | nil => simp [select]
  | cons x xs ih =>
    simp only [select]
    by_cases hP : P (insert x (select P xs).toFinset) <;> simp [hP, ih]

theorem select_sublist_succ {P : Finset α → Prop} [DecidablePred P] {xs : List α} {n : ℕ} :
    select P (xs.rtake n) <+ select P (xs.rtake (n + 1)) := by
  by_cases hn : n < xs.length
  · simp only [rtake_eq_getElem_cons' hn, select]
    by_cases hP : P (insert xs[xs.length - 1 - n] (select P (xs.rtake n)).toFinset) <;> simp [hP]
  · simp [rtake.eq_1, show xs.length - n = xs.length - (n + 1) by omega]

theorem select_monotone {P : Finset α → Prop} [DecidablePred P] {xs : List α} {n m : ℕ}
    (hmn : m ≤ n) : select P (xs.rtake m) <+ select P (xs.rtake n) := by
  induction n with
  | zero => simp [nonpos_iff_eq_zero.mp hmn]
  | succ n ih =>
    by_cases hmn' : m = n + 1
    · simp [hmn']
    · exact Sublist.trans (ih (by omega)) (select_sublist_succ)

theorem select_sublist' {P : Finset α → Prop} [DecidablePred P] {xs : List α} (n : ℕ) :
    select P (xs.rtake n) <+ select P xs := by
  by_cases hn : n ≤ xs.length
  · exact Sublist.trans (select_monotone hn) (by rw [rtake_length])
  · rw [rtake_of_length_le (le_of_lt (Nat.not_le.mp hn))]

theorem select_monotone' {P : Finset α → Prop} [DecidablePred P] (l₁ l₂ : List α) :
    select P l₂ <+ select P (l₁ ++ l₂) := by
  nth_rw 1 [← rtake_right' (show l₂.length = l₂.length by rfl)]
  refine select_sublist' l₂.length

theorem select_sublist_cons {P : Finset α → Prop} [DecidablePred P] {xs : List α} (h : xs ≠ []) :
    select P xs <+ xs.head h :: select P xs.tail := by
  nth_rw 1 [← cons_head_tail h, select.eq_2]
  by_cases hP : P (insert (xs.head h) (select P xs.tail).toFinset) <;> simp [hP]

theorem select_xs_sublist {P : Finset α → Prop} [DecidablePred P] {xs : List α} (n : ℕ) :
    select P xs <+ xs.take (xs.length - n) ++ select P (xs.rtake n) := by
  induction xs with
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
    refine select_xs_sublist (P := P) _

theorem select_mem_of_P {P : Finset α → Prop} [DecidablePred P] {xs : List α} {n : ℕ}
    (hn : n < xs.length)
    (hP : P (insert xs[n] (select P (xs.rtake (xs.length - n - 1))).toFinset)) :
    xs[n] ∈ select P xs := by
  apply Sublist.mem ?_ (select_sublist' (xs.length - n - 1 + 1))
  have : xs.length - 1 - (xs.length - n - 1) = n := by omega
  rw [rtake_eq_getElem_cons' <| by omega, select.eq_2, if_pos ?_]
  · simp [this]
  · simp [this, hP]

theorem select_of_not_mem {P : Finset α → Prop} [DecidablePred P] {x : α} {xs : List α} {n : ℕ}
    (h : x ∉ select P xs) : x ∉ select P (xs.rtake n) := by
  by_contra hc
  grind [select_sublist']

theorem select_ex_P_of_mem {P : Finset α → Prop} [DecidablePred P] {xs : List α} {x : α}
    (h : x ∈ select P xs) :
    ∃ n : ℕ, ∃ hn : n < xs.length, x = xs[n] ∧
    P (insert xs[n] (select P (xs.rtake (xs.length - n - 1))).toFinset) := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have : ∀ m : ℕ, m ≤ xs.length → x ∉ select P (xs.rtake m) := by
    intro m hm; induction m with
    | zero => simp
    | succ m ih =>
      rw [rtake_eq_getElem_cons' (by omega), select.eq_2]
      by_cases hmx : x = xs[xs.length - 1 - m]
      · have := hc (xs.length - 1 - m) (by omega) hmx
        rw [show xs.length - (xs.length - 1 - m) - 1 = m by omega] at this
        rw [if_neg (by simp[this])]
        exact (ih (Nat.le_of_succ_le hm))
      · by_cases hP : P (insert xs[xs.length - 1 - m] (select P (xs.rtake m)).toFinset)
        <;> simp [hP, hmx, ih (Nat.le_of_succ_le hm)]
  specialize this xs.length (by omega)
  rw [rtake_length] at this
  contradiction

theorem select_iff {P : Finset α → Prop} [DecidablePred P] {xs : List α}
    {hl : List.Nodup xs} {n : ℕ} (hn : n < xs.length) :
    xs[n] ∈ select P xs ↔ P (insert xs[n] (select P (xs.rtake (xs.length - n - 1))).toFinset)
    := by
  constructor
  · intro h
    obtain ⟨m, hm1, hm2, hm3⟩ := select_ex_P_of_mem h
    have := (Nodup.getElem_inj_iff hl).mp hm2
    simpa [this]
  · intro h
    exact select_mem_of_P hn h

theorem select_last {P : Finset α → Prop} [DecidablePred P] {x : α} {xs : List α} :
    if P {x} then
      select P (xs ++ [x]) = (select (fun s ↦ P (s ∪ {x})) xs) ++ [x]
    else
      select P (xs ++ [x]) = select P xs
    := by
  induction xs with
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
    [IsTotal α r] [IsTrans α r] (xs : List α) :
    List α := Greedy.select P (xs.mergeSort (fun x y ↦ r x y))

@[simp] theorem selectRel_nil (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] : selectRel P r [] = [] := by
  simp [selectRel]

theorem selectRel_cons_min (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {x : α} {xs : List α}
    (h : ∀ y ∈ xs, r x y ∧ ¬r y x) :
    if P (insert x (selectRel P r xs).toFinset) then
      selectRel P r (x :: xs) = x :: selectRel P r xs
    else
      selectRel P r (x :: xs) = selectRel P r xs
    := by
  simp [selectRel, mergeSort_cons_min h, Greedy.select]

theorem selectRel_cons_max {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs : List α} (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    if P {x} then
      selectRel P r (x :: xs) = selectRel (fun s ↦ P (s ∪ {x})) r xs ++ [x]
    else
      selectRel P r (x :: xs) = selectRel P r xs
    := by
  grind [selectRel, mergeSort_cons_max, select_last]

theorem selectRel_pairwise (P : Finset α → Prop) [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (xs : List α) :
    Pairwise r (selectRel P r xs) := by
  unfold selectRel
  refine List.Pairwise.sublist Greedy.select_sublist ?_
  exact List.pairwise_mergeSort' r xs

theorem selectRel_max_of_antisymm
    {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs : List α} (hxs₁ : xs ≠ []) (hxs₂ : xs.Nodup)
    (ha : ∀ x y, x ∈ xs → y ∈ xs → r x y ∧ r y x → x = y) :
    let x := xs.maxRel r hxs₁
    if P {x} then
      selectRel P r xs = selectRel (fun s ↦ P (s ∪ {x})) r (xs.erase x) ++ [x]
    else
      selectRel P r xs = selectRel P r (xs.erase x)
    := by
  set x := xs.maxRel r hxs₁ with hx
  have h := calc  (x :: (xs.erase x)).mergeSort (fun a b ↦ r a b)
    _ ~ x :: (xs.erase x) := mergeSort_perm (x :: xs.erase x) fun a b ↦ decide (r a b)
    _ ~ xs                := (perm_cons_erase (xs.maxRel_mem r hxs₁)).symm
  simp only [selectRel]
  rw [← mergeSort_unique_of_antisymm ha h (pairwise_mergeSort' r _)]
  simp only [← selectRel.eq_1]
  refine selectRel_cons_max ?_
  intro y hy
  have hy' : x ≠ y := by by_contra hc; rw [hc] at hy; exact (Nodup.not_mem_erase hxs₂) hy
  have h₀ := ha x y (maxRel_mem r hxs₁) (mem_of_mem_erase hy)
  have h₁ := maxRel_nle r hxs₁ y (mem_of_mem_erase hy)
  rw [← hx] at h₁
  cases total_of r x y with
  | inl h₂ => grind
  | inr h₂ => grind

end Greedy

end List
