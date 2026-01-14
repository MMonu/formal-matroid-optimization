import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

open List

theorem List.rtake_eq_getElem_cons {α : Type*} {xs : List α} {n : ℕ} (hn : n < xs.length) :
    xs.rtake (xs.length - n) = xs[n] :: xs.rtake (xs.length - n - 1) := by
  simp only [rtake.eq_1]
  have h1 : (xs.length - (xs.length - n)) = n := by omega
  have h2 : (xs.length - (xs.length - n - 1)) = n + 1 := by omega
  simp [h1, h2]

theorem List.rtake_eq_getElem_cons' {α : Type*} {xs : List α} {n : ℕ} (hn : n < xs.length) :
    xs.rtake (n + 1) = xs[xs.length - 1 - n ]'(by omega) :: xs.rtake (n) := by
  have h1 : (xs.length - (xs.length - 1 - n)) = n + 1 := by omega
  have := rtake_eq_getElem_cons (xs := xs) (n := xs.length - 1 - n) (by omega)
  simp only [h1, add_tsub_cancel_right] at this
  assumption

theorem List.rtake_sublist_cons {α : Type*} {x : α} {xs : List α} {n : ℕ} :
    xs.rtake n <+ (x :: xs).rtake n := by
  simp only [rtake.eq_1, length_cons]
  by_cases hn : xs.length < n
  · simp [Nat.sub_eq_zero_of_le hn, Nat.sub_eq_zero_of_le (Nat.le_of_succ_le hn)]
  · have : xs.length + 1 - n - 1 = xs.length - n := by omega
    rw [drop_cons (by omega), this]

theorem List.rtake_of_length_le {α : Type*} {n : ℕ} {xs : List α} (h : xs.length ≤ n) :
    xs.rtake n = xs := by
  rw [rtake.eq_1, Nat.sub_eq_zero_of_le h, drop_zero]

theorem List.rtake_length {α : Type*} {xs : List α} : xs.rtake xs.length = xs := by
  exact List.rtake_of_length_le (by omega)
