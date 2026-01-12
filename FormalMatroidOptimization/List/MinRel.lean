import Mathlib.Data.List.Basic
import Mathlib.Tactic

def minRel {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    α → α → α :=
  fun a b ↦ if r a b then a else b

@[simp] theorem minRel_left {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} (h : r a b) : minRel r a b = a := by rw [minRel, if_pos h]

@[simp] theorem minRel_right {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} (h : ¬r a b) : minRel r a b = b := by rw [minRel, if_neg h]

@[simp] theorem minRel_or {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} : minRel r a b = b ∨ minRel r a b = a := by
  by_cases hab : r a b <;> simp [minRel, hab]

theorem minRel_assoc {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    ∀ a b c, minRel r (minRel r a b) c = minRel r a (minRel r b c) := by
  intro a b c
  by_cases hab : r a b
  · by_cases hac : r a c
    · by_cases hbc : r b c <;> simp [hab, hac, hbc]
    · by_cases hbc : r b c
      · exact False.elim (hac (Trans.simple hab hbc))
      · simp [hab, hac, hbc]
  · by_cases hac : r a c
    · by_cases hbc : r b c
      · simp [hbc, hab]
      · have hba := (IsTotal.total (r := r) a b).resolve_left hab
        exact False.elim (hbc (Trans.simple hba hac))
    · by_cases hbc : r b c
      · simp [hab, hbc]
      · simp [hab, hac, hbc]

instance minRel_instAssoc {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] : Std.Associative (minRel r) where
  assoc := minRel_assoc r

namespace List

def minRel? {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List α → Option α
  | [] => none
  | x :: xs => some (xs.foldl (minRel r) x)

protected def minRel {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    (lst : List α ) → (h : lst ≠ []) → α
  | x :: xs, _ => xs.foldl (minRel r) x

@[simp] theorem minRel?_nil {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] : [].minRel? r = none := by rfl

theorem minRel?_cons' {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs : List α} :
    (x :: xs).minRel? r = some (foldl (minRel r) x xs) := by rfl

@[simp] theorem minRel?_cons {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {x : α} {xs : List α} :
    (x :: xs).minRel? r = some ((xs.minRel? r).elim x ((minRel r) x)) := by
  cases xs
  · simp [minRel?_cons']
  · simp [minRel?_cons', foldl_assoc]

theorem minRel?_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {lst : List α} {a : α} : lst.minRel? r = some a → a ∈ lst := by
  match lst with
  | [] => simp [minRel?]
  | x :: xs =>
    simp only [minRel?, Option.some.injEq, mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp only [foldl_cons] at eq
      have p := ind _ eq
      cases p with
      | inl p =>
        exact match minRel_or r (a := x) (b := y) with
        | Or.inl h => by simp [p, h]
        | Or.inr h => by simp [p, h]
      | inr p =>
        simp [p]

theorem minRel?_eq_some_min {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {lst : List α} (h : lst ≠ []) : lst.minRel? r = some (lst.minRel r h) := by
  match lst with
  | [] => contradiction
  | x :: xs => simp [List.minRel, minRel?]

theorem minRel_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {lst : List α} (h : lst ≠ []) : lst.minRel r h ∈ lst :=
  minRel?_mem r (minRel?_eq_some_min r h)

end List
