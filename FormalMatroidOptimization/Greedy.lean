import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Sublists
import Mathlib.Tactic
import FormalMatroidOptimization.Rtake

open List
namespace Greedy

/-- Greedily select elements from a list, right to left -/
def select {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) : List α :=
  match lst with
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

def lst : List (Fin 3) := [3, 2, 1]

#eval select P lst

end GreedySelectExample

theorem select_sublist {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) :
  select P lst <+ lst := by
  induction lst with
  | nil => simp [select]
  | cons x xs ih =>
    simp only [select]
    by_cases hP : P (insert x (select P xs).toFinset) = true <;> simp [hP, ih]

theorem select_sublist_succ {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
    {n : ℕ} :
    select P (lst.rtake n) <+ select P (lst.rtake (n + 1)) := by
  by_cases hn : n < lst.length
  · simp only [rtake_eq_getElem_cons' hn, select]
    by_cases hP : P (insert lst[lst.length - 1 - n] (select P (lst.rtake n)).toFinset) <;> simp [hP]
  · have : lst.length - n = lst.length - (n + 1) := by omega
    simp [rtake.eq_1, this]

theorem select_monotone {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
    {n m : ℕ} (hmn : m ≤ n) :
    select P (lst.rtake m) <+ select P (lst.rtake n) := by
  induction n with
  | zero => simp [nonpos_iff_eq_zero.mp hmn]
  | succ n ih =>
    by_cases hmn' : m = n + 1
    · simp [hmn']
    · exact Sublist.trans (ih (by omega)) (select_sublist_succ P lst)

theorem select_sublist' {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) (n : ℕ) :
    select P (lst.rtake n) <+ select P lst := by
  by_cases hn : n ≤ lst.length
  · exact Sublist.trans (select_monotone P lst hn) (by rw [rtake_length])
  · rw [rtake_of_length_le (le_of_lt (Nat.not_le.mp hn))]

theorem select_sublist_cons {α : Type*} [DecidableEq α] (P : Finset α → Bool) {lst : List α}
    (h : lst ≠ []) :
    select P lst <+ lst.head h :: select P lst.tail := by
  nth_rw 1 [← cons_head_tail h, select.eq_2]
  by_cases hP : P (insert (lst.head h) (select P lst.tail).toFinset) <;> simp [hP]

theorem select_lst_sublist {α : Type*} [DecidableEq α] (P : Finset α → Bool) {lst : List α}
    {n : ℕ} :
    select P lst <+ lst.take (lst.length - n) ++ select P (lst.rtake n) := by
  induction lst with
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

theorem select_mem_of_P {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) {n : ℕ}
    (hn : n < lst.length)
    (hP : P (insert lst[n] (select P (lst.rtake (lst.length - n - 1))).toFinset)) :
    lst[n] ∈ select P lst := by
  apply Sublist.mem ?_ (select_sublist' P lst (lst.length - n - 1 + 1))
  have : lst.length - 1 - (lst.length - n - 1) = n := by omega
  rw [rtake_eq_getElem_cons' <| by omega, select.eq_2, if_pos ?_]
  · simp [this]
  · simp [this, hP]

theorem select_ex_P_of_mem {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
    {x : α} (h : x ∈ select P lst) :
    ∃ n : ℕ, ∃ hn : n < lst.length, x = lst[n] ∧
    P (insert lst[n] (select P (lst.rtake (lst.length - n - 1))).toFinset) := by
  by_contra hc
  simp only [not_exists, not_and, Bool.not_eq_true] at hc
  have : ∀ m : ℕ, m ≤ lst.length → x ∉ select P (lst.rtake m) := by
    intro m; induction m with
    | zero => simp [select]
    | succ m ih =>
      intro hm
      rw [rtake_eq_getElem_cons' (by omega), select.eq_2]
      by_cases hmx : x = lst[lst.length - 1 - m]
      · have := hc (lst.length - 1 - m) (by omega) hmx
        rw [show lst.length - (lst.length - 1 - m) - 1 = m by omega] at this
        rw [if_neg (by simp[this])]
        exact (ih (Nat.le_of_succ_le hm))
      · by_cases hP : P (insert lst[lst.length - 1 - m] (select P (lst.rtake m)).toFinset)
        <;> simp [hP, hmx, ih (Nat.le_of_succ_le hm)]
  specialize this lst.length (by omega)
  rw [rtake_length] at this
  contradiction

theorem select_iff {α : Type*} [DecidableEq α] {P : Finset α → Bool} {lst : List α}
    {hl : List.Nodup lst} {n : ℕ} (hn : n < lst.length) :
    lst[n] ∈ select P lst ↔ P (insert lst[n] (select P (lst.rtake (lst.length - n - 1))).toFinset)
    := by
  constructor
  · intro h
    obtain ⟨m, hm1, hm2, hm3⟩ := select_ex_P_of_mem P lst h
    have := (Nodup.getElem_inj_iff hl).mp hm2
    simpa [this]
  · intro h
    exact select_mem_of_P P lst hn h

end Greedy

-- open Classical in
-- noncomputable def GreedyMin {α β : Type*} [DecidableEq α] [LinearOrder β] (F : IndepSystem α)
--   (c : α → β) : List α :=
--   GreedySelect F.Indep (F.E.toList.mergeSort (fun a b ↦ decide (c a ≤ c b)))

-- lemma LE_lift {α β : Type*} [LinearOrder β] (lst : List α) (c : α → β) :
--   ((lst.mergeSort (fun a b ↦ decide (c a ≤ c b))).map c).SortedLE := by
--   let r (a b : α) : Prop := c a ≤ c b
--   let h_total : IsTotal α r := ⟨fun a b ↦ le_total (c a) (c b)⟩
--   let h_trans : IsTrans α r := ⟨fun a b d ha hb ↦ le_trans ha hb⟩
--   have h' : ∀ a b, r a b → c a ≤ c b := by intro a b hrab; unfold r at hrab; assumption
--   have := (List.pairwise_mergeSort' r lst).map c h'
--   exact List.Pairwise.sortedLE this

-- #check List.Pairwise.sublist
-- #check List.isChain_map

-- theorem GreedyMin.sorted {α β : Type*} [DecidableEq α] [LinearOrder β] {F : IndepSystem α}
--   {c : α → β} : ((GreedyMin F c).map c).SortedLE := by
--   let r (a b : α) : Prop := c a ≤ c b
--   let h_total : IsTotal α r := ⟨fun a b ↦ le_total (c a) (c b)⟩
--   let h_trans : IsTrans α r := ⟨fun a b d ha hb ↦ le_trans ha hb⟩
--   have := LE_lift F.E.toList c
--   unfold GreedyMin
--   rw [List.sortedLE_iff_isChain, List.isChain_map] at *
--   rw [List.isChain_iff_pairwise] at *
--   refine List.Pairwise.sublist (?_) this
--   exact GreedySelect.sublist F.Indep (F.E.toList.mergeSort fun a b ↦ decide (c a ≤ c b))
