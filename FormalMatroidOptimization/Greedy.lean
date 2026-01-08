import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

open List

theorem List.rtake_eq_getElem_cons {α : Type*} {lst : List α} {n : ℕ} (hn : n < lst.length) :
    lst.rtake (lst.length - n) = lst[n] :: lst.rtake (lst.length - n - 1) := by
  simp only [rtake.eq_1]
  have h1 : (lst.length - (lst.length - n)) = n := by omega
  have h2 : (lst.length - (lst.length - n - 1)) = n + 1 := by omega
  simp [h1, h2]

theorem List.rtake_eq_getElem_cons' {α : Type*} {lst : List α} {n : ℕ} (hn : n < lst.length) :
    lst.rtake (n + 1) = lst[lst.length - 1 - n ]'(by omega) :: lst.rtake (n) := by
  have h1 : (lst.length - (lst.length - 1 - n)) = n + 1 := by omega
  have := @rtake_eq_getElem_cons α lst (lst.length - 1 - n) (by omega)
  simp only [h1, add_tsub_cancel_right] at this
  assumption

theorem List.rtake_sublist_cons {α : Type*} {x : α} {xs : List α} {n : ℕ} :
    xs.rtake n <+ (x :: xs).rtake n := by
  simp only [rtake.eq_1, length_cons]
  by_cases hn : xs.length < n
  · simp [Nat.sub_eq_zero_of_le hn, Nat.sub_eq_zero_of_le (Nat.le_of_succ_le hn)]
  · have : xs.length + 1 - n - 1 = xs.length - n := by omega
    rw [drop_cons (by omega), this]

example {α : Type*} (lst : List α) {h : lst ≠ []} : lst = lst.head h :: lst.tail := by
  exact Eq.symm (cons_head_tail h)



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

theorem select_sublist {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) :
  select P lst <+ lst := by
  induction lst with
  | nil => simp [select]
  | cons x xs ih =>
    simp only [select]
    by_cases h : P (insert x (select P xs).toFinset) = true
    · simpa [if_pos h]
    · simp [if_neg h, ih]

theorem select_sublist_succ {α : Type*} [DecidableEq α] (P : Finset α → Bool) {lst : List α}
    {n : ℕ} :
    select P (lst.rtake n) <+ select P (lst.rtake (n + 1)) := by
  by_cases hn : n < lst.length
  · simp only [rtake_eq_getElem_cons' hn, select]
    by_cases hP : P (insert lst[lst.length - 1 - n] (select P (lst.rtake n)).toFinset) <;> simp [hP]
  · have : lst.length - n = lst.length - (n + 1) := by omega
    simp [rtake.eq_1, this]

theorem select_monotone {α : Type*} [DecidableEq α] (P : Finset α → Bool) {lst : List α}
    {n m : ℕ} (hmn : m ≤ n) :
    select P (lst.rtake m) <+ select P (lst.rtake n) := by
  induction n with
  | zero => simp [nonpos_iff_eq_zero.mp hmn]
  | succ n ih =>
    by_cases hmn' : m = n + 1
    · simp [hmn']
    · exact Trans.trans (ih (by omega)) (select_sublist_succ P)

theorem select_sublist_cons {α : Type*} [DecidableEq α] (P : Finset α → Bool) {lst : List α}
    (h : lst ≠ []) :
    select P lst <+ lst.head h :: select P lst.tail := by
  nth_rw 1 [← cons_head_tail h, select.eq_2]
  by_cases hP : P (insert (lst.head h) (select P lst.tail).toFinset) <;> simp [hP]

theorem select_sublist' {α : Type*} [DecidableEq α] (P : Finset α → Bool) {lst : List α} {n : ℕ} :
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

-- open List in
-- theorem GreedySelect.select_iff {α : Type*} [DecidableEq α] {P : Finset α → Bool} {lst : List α}
--   {h_lst : List.Nodup lst} (n : Fin lst.length) : lst[n] ∈ select P lst ↔
--   P (insert lst[n] (select P (lst.rtake (lst.length - n - 1))).toFinset) := by
--   induction lst with
--   | nil =>
--     constructor
--     · intro h
--       rw [GreedySelect.eq_1, mem_nil_iff] at h
--       contradiction
--     · intro h
--       simp at n
--       cases n.isLt
--   | cons x xs ih =>
--     have h0 : 0 < (x :: xs).length := by rw [length_cons]; exact Nat.zero_lt_succ xs.length
--     by_cases hxs : xs = []
--     · have bla : n = ⟨0, h0⟩ := by
--           rw [Fin.eq_mk_iff_val_eq]
--           have := Fin.prop n
--           nth_rw 2 [length_cons, hxs] at this
--           rw [length_nil, Nat.zero_add] at this
--           nth_rw 1 [← Nat.lt_one_iff]
--           assumption
--       have bli : [x].toFinset = {x} := by exact Finset.val_eq_singleton_iff.mp rfl
--       constructor
--       · intro h
--         simp [select, hxs] at h ⊢
--         nth_rw 1 [← h.right] at bli
--         rw [← bli] at h
--         exact h.left
--       · intro h
--         simp [select, hxs] at h ⊢
--         have hn : ↑n < [x].length := by
--           rw [length_singleton, bla, Nat.pos_iff_ne_zero]; exact Nat.one_ne_zero
--         have h0' : 0 < [x].length := by rw [length_singleton]; exact Nat.one_pos
--         have : ⟨n, hn⟩ = (⟨0, h0'⟩ : Fin [x].length) := by
--           rw [Fin.mk_eq_mk]
--           exact Fin.eq_mk_iff_val_eq.mp bla
--         have : [x][n]'hn = x := by
--           rw [show [x][n] = [x].get ⟨↑n, hn⟩ from rfl, this]
--           rfl
--         nth_rw 1 [← this]
--         exact ⟨h, this⟩
--     · by_cases hn : n = ⟨0, h0⟩
--       · have : (x :: xs)[n] = x := by rw [hn]; rfl
--         constructor
--         · intro h
--           rw [this] at h ⊢
--           simp [select] at h
--           by_cases hP : P (insert x (select P xs).toFinset)
--           · rw [rtake.eq_1, hn]
--             simp
--             exact hP
--           · rw [if_neg hP] at h
--             have := GreedySelect.sublist P xs
--             apply (List.Sublist.mem) at h
--             specialize h this
--             have := h_lst.notMem
--             contradiction
--         · intro h
--           rw [this] at h ⊢
--           have hn0 : (n : ℕ) = 0 := by exact Fin.eq_mk_iff_val_eq.mp hn
--           rw [rtake.eq_1, Nat.sub_sub, Nat.sub_sub_self ?_] at h
--           rw [hn0, Nat.zero_add, show drop 1 (x :: xs) = xs from rfl] at h
--           simp [select]
--           rw [if_pos h]
--           exact mem_cons_self
--           rw [hn0, Nat.zero_add, length_cons]
--           exact Nat.le_add_left 1 xs.length
--       · have hn' : 0 < (n : ℕ) := by rw [Nat.pos_iff_ne_zero]; rw [Fin.eq_mk_iff_val_eq] at hn; exact hn
--         have : 0 < xs.length := by rw [length_pos_iff]; exact hxs
--         have h1 : 1 < (x :: xs).length := by rw [length_cons]; exact Nat.lt_add_of_pos_left this
--         set k := n - ⟨1, h1⟩ with hk
--         have hk' : k < xs.length := by
--           rw [hk]
--           rw [Fin.sub_val_of_le ?_]
--           apply Nat.sub_one_lt_of_le hn'
--           have := Fin.prop n
--           nth_rw 2 [length_cons] at this
--           exact Fin.is_le n
--           rw [Fin.le_def, Nat.one_le_iff_ne_zero]
--           exact Nat.ne_zero_of_lt hn'
--         have hk'' : k + 1 < (x :: xs).length := by
--           nth_rw 2 [length_cons]
--           rwa [Nat.add_one_lt_add_one_iff]
--         have hk''' : n = ⟨k.val + 1, hk''⟩ := by
--           rw [Fin.ext_iff]
--           rw [show ↑(⟨↑k + 1, hk''⟩ : Fin (x :: xs).length) = ↑k + 1 from rfl]
--           rw [show k = n - ⟨1, h1⟩ from rfl]
--           rw [Fin.sub_val_of_le (Fin.mk_le_of_le_val hn')]
--           rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt hn')]
--         have : (x :: xs).get ⟨k.val + 1, hk''⟩ = xs[k] := by rfl
--         have bl: (x :: xs).get n = xs[k] := by rw [hk''']; exact this
--         set l : Fin xs.length := ⟨k.val, hk'⟩ with hl
--         have hl' : xs[l] = xs[k] := by
--           rw [show xs[l] = xs.get ⟨↑l, hk'⟩ from rfl]
--           rw [show xs[k] = xs.get ⟨↑k, hk'⟩ from rfl]
--         have : xs.Nodup := by exact Nodup.of_cons h_lst
--         specialize @ih this l
--         constructor
--         · intro h
--           rw [show (x :: xs)[n] = (x :: xs).get n from rfl, bl] at h ⊢
--           rw [← hl'] at h ⊢
--           have : xs[l] ∈ x :: select P xs := by
--             apply Sublist.mem h
--             exact (GreedySelect.monotone' P x xs)
--           rw [mem_cons] at this
--           obtain h_1 | h_2 := this
--           · rw [nodup_cons] at h_lst
--             have := h_lst.left
--             rw [show (x ∉ xs) = (x ∈ xs → False) from rfl] at this
--             have ha : xs[l] ∈ xs := by (expose_names; exact mem_of_getElem this_2)
--             rw [h_1] at ha
--             have := this ha
--             contradiction
--           · have ih := ih.mp h_2
--             rw [rtake.eq_1] at ih ⊢
--             rw [← Nat.Simproc.sub_add_eq_comm (x :: xs).length 1 ↑n]
--             rw [tsub_tsub_cancel_of_le (Nat.one_add_le_iff.mpr n.isLt)]
--             rw [drop_cons (Nat.add_pos_right 1 hn')]
--             rw [Nat.one_add_sub_one ↑n]
--             have : l.val + 1 = n.val := by rw [hk''']
--             rw [Nat.sub_sub xs.length (↑l) 1] at ih
--             rw [this] at ih
--             rw [Nat.sub_sub_self (Fin.is_le n)] at ih
--             exact ih
--         · intro h
--           rw [show (x :: xs)[n] = (x :: xs).get n from rfl, bl] at h ⊢
--           rw [← hl'] at h ⊢
--           rw [rtake.eq_1] at ih h
--           rw [← Nat.Simproc.sub_add_eq_comm (x :: xs).length 1 ↑n] at h
--           rw [tsub_tsub_cancel_of_le (Nat.one_add_le_iff.mpr n.isLt)] at h
--           rw [drop_cons (Nat.add_pos_right 1 hn')] at h
--           rw [Nat.one_add_sub_one ↑n] at h
--           rw [Nat.sub_sub xs.length (↑l) 1] at ih
--           rw [Nat.sub_sub_self (Order.add_one_le_iff.mpr hk')] at ih
--           rw [Fin.sub_val_of_le (Fin.mk_le_of_le_val hn')] at ih
--           rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt hn')] at ih
--           have ih := ih.mpr h
--           apply Sublist.mem ih
--           simp [select]
--           by_cases hP' : P (insert x (select P xs).toFinset)
--           · rw [if_pos hP']
--             exact sublist_cons_self x (select P xs)
--           · rw [if_neg hP']

-- namespace GreedySelectExample

-- def P : Finset (Fin 3) → Bool := fun X ↦ match X.card with
-- | 0 => true
-- | 1 => true
-- | 2 => true
-- | _ => false

-- def lst : List (Fin 3) := [3, 2, 1]

-- #eval select P lst

-- end GreedySelectExample

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
