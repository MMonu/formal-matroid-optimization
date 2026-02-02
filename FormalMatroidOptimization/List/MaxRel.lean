import Mathlib.Data.List.Basic

theorem List.Perm.ne_nil_of_ne_nil {α : Type*} {xs ys : List α} (h : xs.Perm ys) :
    xs ≠ [] → ys ≠ [] := by
  intro hi
  by_contra hc
  rw [hc] at h
  exact hi (List.Perm.eq_nil h)

def maxRel {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    α → α → α :=
  fun a b ↦ if r a b then b else a

@[simp] theorem maxRel_left {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} : r a b → maxRel r a b = b := by intro h; rw [maxRel, if_pos h]

@[simp] theorem maxRel_right {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} : ¬r a b → maxRel r a b = a := by intro h; rw [maxRel, if_neg h]

@[simp] theorem maxRel_or {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {a b : α} : maxRel r a b = b ∨ maxRel r a b = a := by
  by_cases hab : r a b <;> simp [maxRel, hab]

theorem maxRel_assoc {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    ∀ a b c, maxRel r (maxRel r a b) c = maxRel r a (maxRel r b c) := by
  intro a b c
  by_cases hab : r a b
  · by_cases hac : r a c
    · by_cases hbc : r b c <;> simp [hab, hac, hbc]
    · by_cases hbc : r b c
      · exact False.elim (hac (Trans.simple hab hbc))
      · simp [hab, hbc]
  · by_cases hac : r a c
    · by_cases hbc : r b c
      · simp [hbc, hab]
      · have hba := (IsTotal.total (r := r) a b).resolve_left hab
        exact False.elim (hbc (Trans.simple hba hac))
    · by_cases hbc : r b c
      · simp [hab, hbc]
      · simp [hab, hac, hbc]

instance maxRel_instAssoc {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] : Std.Associative (maxRel r) where
  assoc := maxRel_assoc r

namespace List

def maxRel? {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    List α → Option α
  | [] => none
  | x :: xs => some (xs.foldl (maxRel r) x)

protected def maxRel {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] :
    (lst : List α ) → (h : lst ≠ []) → α
  | x :: xs, _ => xs.foldl (maxRel r) x

theorem maxRel_singleton {α : Type} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} : [x].maxRel r (by intro h; cases h) = x := by rfl

@[simp] theorem maxRel?_nil {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] : [].maxRel? r = none := by rfl

theorem maxRel?_cons' {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs : List α} :
    (x :: xs).maxRel? r = some (foldl (maxRel r) x xs) := by rfl

@[simp] theorem maxRel?_cons {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {x : α} {xs : List α} :
    (x :: xs).maxRel? r = some ((xs.maxRel? r).elim x ((maxRel r) x)) := by
  cases xs
  · simp [maxRel?_cons']
  · simp [maxRel?_cons', foldl_assoc]

theorem maxRel?_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {lst : List α} {a : α} : lst.maxRel? r = some a → a ∈ lst := by
  match lst with
  | [] => simp [maxRel?]
  | x :: xs =>
    simp only [maxRel?, Option.some.injEq, mem_cons]
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
        exact match maxRel_or r (a := x) (b := y) with
        | Or.inl h => by simp [p, h]
        | Or.inr h => by simp [p, h]
      | inr p =>
        simp [p]

theorem maxRel?_eq_some_max {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {lst : List α} (h : lst ≠ []) : lst.maxRel? r = some (lst.maxRel r h) := by
  match lst with
  | [] => contradiction
  | x :: xs => simp [List.maxRel, maxRel?]

@[simp]
theorem maxRel_mem {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {lst : List α} (h : lst ≠ []) : lst.maxRel r h ∈ lst :=
  maxRel?_mem r (maxRel?_eq_some_max r h)

theorem maxRel_with_max {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {x : α} {xs : List α} (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    (x :: xs).maxRel r (List.cons_ne_nil x xs) = x := by
  by_cases h' : xs = []
  · rw [h']
    rfl
  · have : (x :: xs).maxRel r (List.cons_ne_nil x xs) = (x :: xs).maxRel? r := by
      rw [maxRel?_eq_some_max]
    simp at this
    simp only [this]
    rw [maxRel?_eq_some_max r h', Option.elim_some, maxRel_right r ?_]
    exact (h (xs.maxRel r h') (maxRel_mem r h')).right

theorem maxRel_nle {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] {xs : List α} (h : xs ≠ []) :
    ∀ x ∈ xs, r (xs.maxRel r h) x → r x (xs.maxRel r h) := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    have := maxRel?_eq_some_max r h
    rw [maxRel?_cons r, Option.some_inj] at this
    rw [← this]
    by_cases hy : ys = []
    · simp [hy]
    · rw [maxRel?_eq_some_max r hy, Option.elim_some]
      intro x hx₀ hx₁
      by_cases h₁ : r y (List.maxRel r ys hy)
      · rw [maxRel_left r h₁] at hx₁ ⊢
        by_cases h₂ : x = y
        · rwa [h₂]
        · have hx₀ := Or.resolve_left (mem_cons.mp hx₀) h₂
          exact ih hy x hx₀ hx₁
      · rw [maxRel_right r h₁] at hx₁ ⊢
        by_cases h₂ : x = y
        · rwa [h₂] at hx₁ ⊢
        · have hx₀ := Or.resolve_left (mem_cons.mp hx₀) h₂
          have h₁ := Or.resolve_left (total_of r y (List.maxRel r ys hy)) h₁
          exact Trans.simple (ih hy x hx₀ (Trans.simple h₁ hx₁)) h₁

theorem maxRel?_unique_of_antisymm {α : Type*}
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs ys : List α}
    (ha : ∀ x ∈ xs, ∀ y ∈ xs, r x y ∧ r y x → x = y) (h : ys ~ xs) :
    xs.maxRel? r = ys.maxRel? r  := by
  by_cases hxs : xs = []
  · simp [hxs, perm_nil] at h
    simp [hxs, h]
  · have hys : ys ≠ [] := by
      rw [ne_nil_iff_length_pos, Perm.length_eq h]; simp [length_pos_iff, hxs]
    rw [maxRel?_eq_some_max r hxs, maxRel?_eq_some_max r hys, Option.some_inj]
    have h₀ : ys.maxRel r hys ∈ xs := (Perm.mem_iff h).mp (maxRel_mem r hys)
    have h₁ : xs.maxRel r hxs ∈ ys := (Perm.mem_iff h).mpr (maxRel_mem r hxs)
    have ha := ha (List.maxRel r xs hxs) (maxRel_mem r hxs) (List.maxRel r ys hys) h₀
    have := total_of r (List.maxRel r xs hxs) (List.maxRel r ys hys)
    cases this with
    | inl h₂ => exact ha ⟨h₂, maxRel_nle r hxs _ h₀ h₂⟩
    | inr h₂ => exact ha ⟨maxRel_nle r hys _ h₁ h₂, h₂⟩

theorem maxRel_unique_of_antisymm {α : Type*}
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs ys : List α}
    (ha : ∀ x ∈ xs, ∀ y ∈ xs, r x y ∧ r y x → x = y) (h : ys ~ xs) (hxs : xs ≠ []) :
    xs.maxRel r hxs = ys.maxRel r (by by_contra hc; rw [hc] at h; exact hxs (Perm.eq_nil h.symm))
    := by
  have hys : ys ≠ [] := by by_contra hc; rw [hc] at h; exact hxs (Perm.eq_nil h.symm)
  have := maxRel?_unique_of_antisymm r ha h
  rwa [maxRel?_eq_some_max r hxs, maxRel?_eq_some_max r hys, Option.some_inj] at this

end List
