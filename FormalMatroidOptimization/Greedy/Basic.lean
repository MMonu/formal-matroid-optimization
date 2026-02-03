import FormalMatroidOptimization.List.MaxRel
import FormalMatroidOptimization.List.Greedy
import FormalMatroidOptimization.FinMatroid.Basic

/-!
# Greedy selection using least elements

Two finite sets are stored for the greedy selection, the elements that have not been considered yet,
and those already selected. Then at each iteration a least element with respect to the given
relation is considered, this is unique if the relation is antisymmetric on the elements to be
considered

## Main Definitions / Theorems

* `selectRel_internal P r l₁ l₂` Greedily select elements of `l₁`, based on the predicate `P` and
  `l₂` already selected, the order based on the relation `r`

* `selectRel P r l₁` Greedily select elements of `l₁`, based on the predicate `P` the order based
  on the relation `r`

* `selectRel_internal_prop P r` At any point where `l₂` have been selected, remaining selection may
  is equal to selection with a modified predicate appended by `l₂`

* `selectRel_eq_list_selectRel r hn ha` Given a proof `ha` for antisymmetry of the relation `r` the
  greedy selection defined here is equal to greedy selection using mergeSort.
-/

open List

namespace Greedy

variable {α : Type*} [DecidableEq α]

def selectRel_internal (P : Finset α → Prop) [DecidablePred P] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l₁ l₂ : List α) : List α :=
  let sP := l₁.filter (fun x ↦ P (insert x l₂.toFinset))
  if hsP : sP ≠ [] then
    let y := sP.maxRel r hsP
    selectRel_internal P r (l₁.erase y) (y :: l₂)
  else
    l₂
  termination_by
    l₁.length
  decreasing_by
    apply Order.lt_of_succ_lt_succ
    rw [Order.succ_eq_add_one, List.length_erase_add_one ?_]
    · simp
    · have : (filter (fun x ↦ P (insert (↑x) l₂.toFinset)) l₁.attach).unattach ⊆ l₁ := by
        intro z hz; simp at hz; exact hz.left
      exact this (maxRel_mem r hsP)

def selectRel (P : Finset α → Prop) [DecidablePred P] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l₁ : List α) : List α :=
  selectRel_internal P r l₁ []

@[simp] theorem selectRel_nil {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] : selectRel P r [] = [] := by
  simp [selectRel, selectRel_internal]


theorem selectRel_internal_subset {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] {l₁ l₂ : List α} :
    l₂ ⊆ selectRel_internal P r l₁ l₂ := by
  match l₁ with
  | [] =>
    grind [selectRel_internal]
  | x :: l₁ =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x l₂.toFinset))) (x :: l₁) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      exact subset_of_cons_subset (selectRel_internal_subset
        (l₁ := ((x :: l₁).erase (List.maxRel r sP hsP₂))) (l₂ := ((List.maxRel r sP hsP₂) :: l₂)))
    · rw [dif_neg hsP₂]
      simp
  termination_by
    l₁.length
  decreasing_by
    grind [maxRel_mem]

theorem selectRel_internal_indep {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l₁ l₂ : List α} (hl₂ : P l₂.toFinset) :
    P (selectRel_internal P r l₁ l₂).toFinset := by
  match l₁ with
  | [] =>
    grind [selectRel_internal]
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x l₂.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      apply (selectRel_internal_indep
        (l₁ := ((x :: xs).erase (List.maxRel r sP hsP₂))) (l₂ := ((List.maxRel r sP hsP₂) :: l₂)))
      have := (mem_filter.mp (maxRel_mem r hsP₂)).right
      rw [Bool.decide_iff] at this
      simpa
    · rwa [dif_neg hsP₂]
  termination_by
    l₁.length
  decreasing_by
    grind [maxRel_mem]

lemma selectRel_internal_maximal {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] {l₁ l₂ : List α} :
    ∀ x ∈ l₁, x ∉ (Greedy.selectRel_internal P r l₁ l₂).toFinset →
    ¬ P (insert x (Greedy.selectRel_internal P r l₁ l₂).toFinset) := by
  match l₁ with
  | [] =>
    grind [selectRel_internal]
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x l₂.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      intro x₁ hx₁
      by_cases hx₁y : x₁ ≠ List.maxRel r sP hsP₂
      · apply (selectRel_internal_maximal (l₁ := ((x :: xs).erase (List.maxRel r sP hsP₂)))
        (l₂ := ((List.maxRel r sP hsP₂) :: l₂)))
        exact (mem_erase_of_ne hx₁y).mpr hx₁
      · rw [not_not] at hx₁y
        set y := List.maxRel r sP hsP₂ with hy
        have hxin : y ∈ List.maxRel r sP hsP₂ :: l₂ := mem_cons_self
        intro h
        have hl₂ : (y :: l₂) ⊆ selectRel_internal P r ((x :: xs).erase y) (y :: l₂) := by
          grind [selectRel_internal_subset]
        have : x₁ ∈ (selectRel_internal P r ((x :: xs).erase y) (y :: l₂)) := by
          grind only [= subset_def]
        have : x₁ ∈ (selectRel_internal P r ((x :: xs).erase y) (y :: l₂)).toFinset := by
          exact mem_toFinset.mpr this
        contradiction
    · simp_all
  termination_by
    l₁.length
  decreasing_by
    · grind [maxRel_mem]

theorem selectRel_internal_prop
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l₁ l₂ : List α} :
    selectRel_internal P r l₁ l₂ = (selectRel_internal (fun s ↦ P (s ∪ l₂.toFinset)) r l₁ []) ++ l₂
    := by
  rw [selectRel_internal.eq_def, selectRel_internal.eq_def]
  set sP := filter (fun x ↦ decide (P (insert x l₂.toFinset))) l₁ with hsP₁
  have : sP = filter (fun x ↦ decide (P (insert x [].toFinset ∪ l₂.toFinset))) l₁ := by rfl
  rw [← this]
  by_cases hsP₂ : sP ≠ []
  · rw [dif_pos hsP₂, dif_pos hsP₂]
    have := selectRel_internal_prop (r := r) (l₁ := (l₁.erase (List.maxRel r sP hsP₂)))
      (l₂ := (List.maxRel r sP hsP₂) :: l₂) hP
    rw [this]
    set P₁ := fun s ↦ P (s ∪ l₂.toFinset) with hP₁
    have hP₂ : IndepSystem.HereditaryProperty P₁ := by
      intro X Y hX hXY
      simp only [hP₁] at hX ⊢
      have : (Y ∪ l₂.toFinset) ⊆ (X ∪ l₂.toFinset) := by grind
      exact hP hX this
    have := selectRel_internal_prop (r := r) (l₁ := (l₁.erase (List.maxRel r sP hsP₂)))
      (l₂ := [List.maxRel r sP hsP₂]) hP₂
    rw [this, ← singleton_append, append_assoc]
    congr
    ext x
    simp [hP₁]
  · rw [dif_neg hsP₂, dif_neg hsP₂]
    simp
  termination_by
    l₁.length
  decreasing_by
    · grind [maxRel_mem]
    · grind [maxRel_mem]

theorem selectRel_internal_eq_selectRel_prop
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l₁ l₂ : List α} :
    selectRel_internal P r l₁ l₂ = (selectRel (fun s ↦ P (s ∪ l₂.toFinset)) r l₁) ++ l₂
    := by
  rw [selectRel]
  exact selectRel_internal_prop hP

theorem selectRel_internal_cons_max
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {l₁ l₂ : List α} (h : ∀ y ∈ l₁, r y x ∧ ¬r x y) :
    if P (insert x l₂.toFinset) then
      selectRel_internal P r (x :: l₁) l₂ = selectRel_internal P r l₁ (x :: l₂)
    else
      selectRel_internal P r (x :: l₁) l₂ = selectRel_internal P r l₁ l₂
    := by
  rw [selectRel_internal]
  set sP := filter (fun x ↦ decide (P (insert x l₂.toFinset))) (x :: l₁) with hsP₁
  by_cases hx : x ∈ sP
  · have hP₁ := (Bool.decide_iff _).mp (List.mem_filter.mp hx).right
    rw [if_pos hP₁]
    have hl₁P : x ∈ sP := by simp [hsP₁, hP₁]
    have hsP₂ : sP ≠ [] := by by_contra; apply List.not_mem_nil; rwa [this] at hl₁P
    rw [dif_pos hsP₂]
    have : ∀ y ∈ filter (fun x ↦ decide (P (insert x l₂.toFinset))) l₁, r y x ∧ ¬r x y := by grind
    have : List.maxRel r sP hsP₂ = x := by rw [← (maxRel_with_max r this)]; grind
    grind
  · have hP₁ : ¬P (insert x l₂.toFinset) := by grind
    rw [filter_cons_of_neg (by simp [hP₁])] at hsP₁
    rw [if_neg hP₁, selectRel_internal, ← hsP₁]
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂, dif_pos hsP₂]
      set y := List.maxRel r sP hsP₂ with hy₁
      have : (x :: l₁).erase y = x :: l₁.erase y := by
        rw [erase_cons_tail ?_]
        have := Finset.forall_mem_not_eq.mpr ((not_iff_not.mpr (List.mem_toFinset)).mpr hx)
        simp [hy₁, (this (List.maxRel r sP hsP₂) (by simp [maxRel_mem r hsP₂]))]
      have  h' := selectRel_internal_cons_max hP ?_
        (r := r) (x := x) (l₁ := l₁.erase y) (l₂ := y :: l₂)
      · by_cases hP₂ : P (insert x (y :: l₂).toFinset)
        · have : (insert x l₂.toFinset) ⊆ (insert x (y :: l₂).toFinset) := by simp
          exact False.elim (hP₁ (hP hP₂ this))
        · grind
      · grind
    · grind
  termination_by
    l₁.length
  decreasing_by
    grind [maxRel_mem]

theorem selectRel_cons_max
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {l₁ : List α} (h : ∀ y ∈ l₁, r y x ∧ ¬r x y) :
    if P {x} then
      selectRel P r (x :: l₁) = selectRel (fun s ↦ P (s ∪ {x})) r l₁ ++ [x]
    else
      selectRel P r (x :: l₁) = selectRel P r l₁
    := by
  unfold selectRel
  have := selectRel_internal_cons_max hP h (l₂ := [])
  have h₁ : (insert x [].toFinset) = {x} := by rw [toFinset_nil, insert_empty_eq]
  rw [h₁] at this
  by_cases hP₁ : P {x}
  · rw [if_pos hP₁] at this ⊢
    simp [this, selectRel_internal_prop hP]
  · rwa [if_neg hP₁] at this ⊢

theorem selectRel_internal_unique_of_antisymm {P : Finset α → Prop} [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {l₁ l₂ : List α} (l₃ : List α)
    (ha : ∀ x y, x ∈ l₁ → y ∈ l₁ → r x y ∧ r y x → x = y) (h : l₂ ~ l₁) :
    selectRel_internal P r l₁ l₃ = selectRel_internal P r l₂ l₃ := by
  rw [selectRel_internal, selectRel_internal]
  set p := fun x ↦ decide (P (insert x l₃.toFinset)) with hp
  by_cases hsP₁ : filter p l₁ ≠ []
  · rw [dif_pos hsP₁, dif_pos (Perm.ne_nil_of_ne_nil (Perm.filter p h.symm) hsP₁)]
    rw [maxRel_unique_of_antisymm r (by grind) (Perm.filter p h) hsP₁]
    rw [selectRel_internal_unique_of_antisymm r _ (by grind) (Perm.erase _ h)]
  · rw [dif_neg hsP₁, dif_neg (?_)]
    rw [not_ne_iff] at hsP₁ ⊢
    apply Perm.eq_nil
    exact (Perm.filter p h).trans (by rw[hsP₁])
  termination_by
    l₁.length
  decreasing_by
    grind [maxRel_mem]

theorem selectRel_max_of_antisymm
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l : List α} (hl₁ : l ≠ []) (hl₂ : l.Nodup)
    (ha : ∀ x y, x ∈ l → y ∈ l → r x y ∧ r y x → x = y) :
    let x := l.maxRel r hl₁
    if P {x} then
      selectRel P r l = selectRel (fun s ↦ P (s ∪ {x})) r (l.erase x) ++ [x]
    else
      selectRel P r l = selectRel P r (l.erase x)
    := by
  set x := List.maxRel r l hl₁ with hx
  have heq : x :: (l.erase x) ~ l := by grind [cons_perm_iff_perm_erase, maxRel_mem r hl₁]
  simp only [selectRel]
  rw [selectRel_internal_unique_of_antisymm r [] ha heq]
  simp only [← selectRel.eq_1]
  have := selectRel_cons_max hP ?_ (r := r) (x := x) (l₁ := l.erase x)
  · simpa
  · intro y hy
    have hy' : x ≠ y := by by_contra hc; rw [hc] at hy; exact (Nodup.not_mem_erase hl₂) hy
    have h₀ := ha x y (maxRel_mem r hl₁) (mem_of_mem_erase hy)
    have h₁ := maxRel_nle r hl₁ y (mem_of_mem_erase hy)
    rw [← hx] at h₁
    cases total_of r x y with
    | inl h₂ => grind
    | inr h₂ => grind

theorem selectRel_eq_list_selectRel
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {l : List α} (hl : l.Nodup) (ha : ∀ x y, x ∈ l → y ∈ l → r x y ∧ r y x → x = y) :
    selectRel P r l = List.Greedy.selectRel P r l := by
  by_cases hl₁₁ : l = []
  · simp [hl₁₁]
  · set x := List.maxRel r l hl₁₁ with hx
    have h₁ := selectRel_max_of_antisymm hP hl₁₁ hl ha
    have h₂ := List.Greedy.selectRel_max_of_antisymm (P := P) hl₁₁ hl ha
    by_cases hP₁ : P {List.maxRel r l hl₁₁}
    <;> simp only [hP₁, ↓reduceIte, Finset.union_singleton] at h₁ h₂
    <;> rw [h₁, h₂, selectRel_eq_list_selectRel (by intro l₂ zs hz hzy; exact hP hz (by grind))]
    <;> grind
  termination_by
    l.length
  decreasing_by
    · grind [maxRel_mem]
    · grind [maxRel_mem]

end Greedy
