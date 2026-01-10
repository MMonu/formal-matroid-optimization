import Mathlib.Data.List.Basic
import Mathlib.Tactic

def min_rel {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    α → α → α :=
  fun a b ↦ if r a b then a else b

@[simp] theorem min_rel_left {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} (h : r a b) : min_rel r a b = a := by rw [min_rel, if_pos h]

@[simp] theorem min_rel_right {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} (h : ¬r a b) : min_rel r a b = b := by rw [min_rel, if_neg h]

@[simp] theorem min_rel_or {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} : min_rel r a b = b ∨ min_rel r a b = a := by
  by_cases hab : r a b <;> simp [min_rel, hab]

theorem min_rel_assoc {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    ∀ a b c, min_rel r (min_rel r a b) c = min_rel r a (min_rel r b c) := by
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

instance min_rel_instAssoc {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] : Std.Associative (min_rel r) where
  assoc := min_rel_assoc r

namespace List

def min_rel? {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List α → Option α
  | [] => none
  | x :: xs => some (xs.foldl (min_rel r) x)

protected def min_rel {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    (lst : List α ) → (h : lst ≠ []) → α
  | x :: xs, _ => xs.foldl (min_rel r) x

@[simp] theorem min_rel?_nil {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] : [].min_rel? r = none := by rfl

theorem min_rel?_cons' {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs : List α} :
    (x :: xs).min_rel? r = some (foldl (min_rel r) x xs) := by rfl

@[simp] theorem min_rel?_cons {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {x : α} {xs : List α} :
    (x :: xs).min_rel? r = some ((xs.min_rel? r).elim x ((min_rel r) x)) := by
  cases xs
  · simp [min_rel?_cons']
  · simp [min_rel?_cons', foldl_assoc]

theorem min_rel?_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {lst : List α} {a : α} : lst.min_rel? r = some a → a ∈ lst := by
  match lst with
  | [] => simp [min_rel?]
  | x :: xs =>
    simp only [min_rel?, Option.some.injEq, mem_cons]
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
        exact match min_rel_or r (a := x) (b := y) with
        | Or.inl h => by simp [p, h]
        | Or.inr h => by simp [p, h]
      | inr p =>
        simp [p]

theorem min_rel?_eq_some_min {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {lst : List α} (h : lst ≠ []) : lst.min_rel? r = some (lst.min_rel r h) := by
  match lst with
  | [] => contradiction
  | x :: xs => simp [List.min_rel, min_rel?]

theorem min_rel_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {lst : List α} (h : lst ≠ []) : lst.min_rel r h ∈ lst :=
  min_rel?_mem r (min_rel?_eq_some_min r h)

end List
