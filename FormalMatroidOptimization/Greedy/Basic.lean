import FormalMatroidOptimization.List.MaxRel
import FormalMatroidOptimization.List.Greedy
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
    grind [maxRel_mem]

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
    grind [maxRel_mem]

lemma selectRel_internal_maximal {P : Finset α → Prop} [DecidablePred P]
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs ys : List α} :
    ∀ x ∈ xs, x ∉ (Greedy.selectRel_internal P r xs ys).toFinset →
    ¬ P (insert x (Greedy.selectRel_internal P r xs ys).toFinset) := by
  match xs with
  | [] =>
    grind [selectRel_internal]
  | x :: xs =>
    rw [selectRel_internal.eq_def]
    set sP := filter (fun x ↦ decide (P (insert x ys.toFinset))) (x :: xs) with hsP₁
    by_cases hsP₂ : sP ≠ []
    · rw [dif_pos hsP₂]
      intro x₁ hx₁
      by_cases hx₁y : x₁ ≠ List.maxRel r sP hsP₂
      · apply (selectRel_internal_maximal (xs := ((x :: xs).erase (List.maxRel r sP hsP₂)))
        (ys := ((List.maxRel r sP hsP₂) :: ys)))
        exact (mem_erase_of_ne hx₁y).mpr hx₁
      · rw [not_not] at hx₁y
        set y := List.maxRel r sP hsP₂ with hy
        have hxin : y ∈ List.maxRel r sP hsP₂ :: ys := mem_cons_self
        intro h
        have hys : (y :: ys) ⊆ selectRel_internal P r ((x :: xs).erase y) (y :: ys) := by
          grind [selectRel_internal_subset]
        have : x₁ ∈ (selectRel_internal P r ((x :: xs).erase y) (y :: ys)) := by
          grind only [= subset_def]
        have : x₁ ∈ (selectRel_internal P r ((x :: xs).erase y) (y :: ys)).toFinset := by
          exact mem_toFinset.mpr this
        contradiction
    · simp_all
  termination_by
    xs.length
  decreasing_by
    · grind [maxRel_mem]

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
    · grind [maxRel_mem]
    · grind [maxRel_mem]

theorem selectRel_internal_eq_selectRel_prop
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs ys : List α} :
    selectRel_internal P r xs ys = (selectRel (fun s ↦ P (s ∪ ys.toFinset)) r xs) ++ ys
    := by
  rw [selectRel]
  exact selectRel_internal_prop hP

theorem selectRel_internal_cons_max
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
      have  h' := selectRel_internal_cons_max hP ?_
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
    grind [maxRel_mem]

theorem selectRel_cons_max
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {x : α} {xs : List α} (h : ∀ y ∈ xs, r y x ∧ ¬r x y) :
    if P {x} then
      selectRel P r (x :: xs) = selectRel (fun s ↦ P (s ∪ {x})) r xs ++ [x]
    else
      selectRel P r (x :: xs) = selectRel P r xs
    := by
  unfold selectRel
  have := selectRel_internal_cons_max hP h (ys := [])
  have h₁ : (insert x [].toFinset) = {x} := by rw [toFinset_nil, insert_empty_eq]
  rw [h₁] at this
  by_cases hP₁ : P {x}
  · rw [if_pos hP₁] at this ⊢
    simp [this, selectRel_internal_prop hP]
  · rwa [if_neg hP₁] at this ⊢

theorem selectRel_internal_unique_of_antisymm {P : Finset α → Prop} [DecidablePred P]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] {xs ys : List α} (zs : List α)
    (ha : ∀ x y, x ∈ xs → y ∈ xs → r x y ∧ r y x → x = y) (h : ys ~ xs) :
    selectRel_internal P r xs zs = selectRel_internal P r ys zs := by
  rw [selectRel_internal, selectRel_internal]
  set p := fun x ↦ decide (P (insert x zs.toFinset)) with hp
  by_cases hsP₁ : filter p xs ≠ []
  · rw [dif_pos hsP₁, dif_pos (Perm.ne_nil_of_ne_nil (Perm.filter p h.symm) hsP₁)]
    rw [maxRel_unique_of_antisymm r (by grind) (Perm.filter p h) hsP₁]
    rw [selectRel_internal_unique_of_antisymm r _ (by grind) (Perm.erase _ h)]
  · rw [dif_neg hsP₁, dif_neg (?_)]
    rw [not_ne_iff] at hsP₁ ⊢
    apply Perm.eq_nil
    exact (Perm.filter p h).trans (by rw[hsP₁])
  termination_by
    xs.length
  decreasing_by
    grind [maxRel_mem]

theorem selectRel_max_of_antisymm
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs : List α} (hxs₁ : xs ≠ []) (hxs₂ : xs.Nodup)
    (ha : ∀ x y, x ∈ xs → y ∈ xs → r x y ∧ r y x → x = y) :
    let x := xs.maxRel r hxs₁
    if P {x} then
      selectRel P r xs = selectRel (fun s ↦ P (s ∪ {x})) r (xs.erase x) ++ [x]
    else
      selectRel P r xs = selectRel P r (xs.erase x)
    := by
  set x := List.maxRel r xs hxs₁ with hx
  have heq : x :: (xs.erase x) ~ xs := by grind [cons_perm_iff_perm_erase, maxRel_mem r hxs₁]
  simp only [selectRel]
  rw [selectRel_internal_unique_of_antisymm r [] ha heq]
  simp only [← selectRel.eq_1]
  have := selectRel_cons_max hP ?_ (r := r) (x := x) (xs := xs.erase x)
  · simpa
  · intro y hy
    have hy' : x ≠ y := by by_contra hc; rw [hc] at hy; exact (Nodup.not_mem_erase hxs₂) hy
    have h₀ := ha x y (maxRel_mem r hxs₁) (mem_of_mem_erase hy)
    have h₁ := maxRel_nle r hxs₁ y (mem_of_mem_erase hy)
    rw [← hx] at h₁
    cases total_of r x y with
    | inl h₂ => grind
    | inr h₂ => grind

theorem selectRel_eq_list_selectRel
    {P : Finset α → Prop} [DecidablePred P] (hP : IndepSystem.HereditaryProperty P)
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    {xs : List α} (hxs : xs.Nodup) (ha : ∀ x y, x ∈ xs → y ∈ xs → r x y ∧ r y x → x = y) :
    selectRel P r xs = List.Greedy.selectRel P r xs := by
  by_cases hxs₁ : xs = []
  · simp [hxs₁]
  · set x := List.maxRel r xs hxs₁ with hx
    have h₁ := selectRel_max_of_antisymm hP hxs₁ hxs ha
    have h₂ := List.Greedy.selectRel_max_of_antisymm (P := P) hxs₁ hxs ha
    by_cases hP₁ : P {List.maxRel r xs hxs₁}
    <;> simp only [hP₁, ↓reduceIte, Finset.union_singleton] at h₁ h₂
    <;> rw [h₁, h₂, selectRel_eq_list_selectRel (by intro ys zs hz hzy; exact hP hz (by grind))]
    <;> grind
  termination_by
    xs.length
  decreasing_by
    · grind [maxRel_mem]
    · grind [maxRel_mem]

end Greedy
