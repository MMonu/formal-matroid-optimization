import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

def IndepSystem.HereditaryProperty {α : Type*} (P : Finset α → Bool) : Prop :=
  ∀ ⦃X Y⦄, P X → Y ⊆ X → P Y

def IndepSystem.AugmentationProperty {α : Type*} [DecidableEq α] (P : Finset α → Bool) : Prop :=
  ∀ ⦃X Y⦄, P X → P Y → X.card > Y.card → ∃ x ∈ X, x ∉ Y ∧ P (insert x Y)

structure IndepSystem (α : Type*) where
  /-- Independent system has a ground set `E` -/
  (E : Finset α)
  /-- Independent system has a predicate `Indep` defining its independent sets -/
  (Indep : Finset α → Bool)
  /-- The empty set is `Indep`endent -/
  (indep_empty : Indep ∅)
  /-- For any `Indep`endent set `X`, all its subsets are also `Indep`endent -/
  (indep_subset : IndepSystem.HereditaryProperty Indep)
  /-- All `Indep`endent sets are subsets of the ground set -/
  (subset_ground : ∀ ⦃X⦄, Indep X → X ⊆ E)

structure FinMatroid (α : Type*) [DecidableEq α] extends IndepSystem α where
  /-- For any `Indep`endent sets `X` and `Y` with `Y` smaller than `X`, there exists an element in
  `X` not in `Y` with `Y ∪ {x}` `Indep`endent -/
  (indep_aug : IndepSystem.AugmentationProperty Indep)

noncomputable def FinMatroid.toMatroid {α : Type*} [DecidableEq α] (M : FinMatroid α) :
  Matroid α := by
  let Indep' (X : Set α) : Prop := ∃ hX : X.Finite, M.Indep hX.toFinset
  refine IndepMatroid.matroid (IndepMatroid.ofFinite (M.E.finite_toSet)
    (Indep') (?_) (?_) (?_) (?_))
  · simp [Indep', M.indep_empty]
  · intro I J ⟨hJ_Fin, hJ_Indep⟩ hIJ
    have hI_Fin : I.Finite := by exact Set.Finite.subset hJ_Fin hIJ
    use hI_Fin
    have : hI_Fin.toFinset ⊆ hJ_Fin.toFinset := Set.Finite.toFinset_subset_toFinset.mpr hIJ
    exact M.indep_subset hJ_Indep this
  · intro I J ⟨hI_Fin, hI_Indep⟩ ⟨hJ_Fin, hJ_Indep⟩ hcard
    have : hI_Fin.toFinset.card < hJ_Fin.toFinset.card := by
      rwa [← Set.ncard_eq_toFinset_card I hI_Fin, ← Set.ncard_eq_toFinset_card J hJ_Fin]
    obtain ⟨x, hxJ, hxI, hx⟩ := M.indep_aug hJ_Indep hI_Indep this
    use x
    constructor
    · exact (Set.Finite.mem_toFinset hJ_Fin).mp hxJ
    · constructor
      · rwa [← Set.Finite.mem_toFinset hI_Fin]
      · have hxI' : (insert x I).Finite := by exact Set.finite_insert.mpr hI_Fin
        use hxI'
        rwa [Set.Finite.toFinset_insert hxI']
  · intro I ⟨hI_Fin, hI_Indep⟩
    exact Set.Finite.toFinset_subset.mp (M.subset_ground hI_Indep)

/-- Greedily select elements from a list, right to left -/
def GreedySelect {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) : List α :=
  match lst with
  | []      => []
  | x :: xs =>
    if P (insert x (GreedySelect P xs).toFinset) then
      x :: (GreedySelect P xs)
    else
      GreedySelect P xs

open List in
theorem GreedySelect.sublist {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α) :
  GreedySelect P lst <+ lst := by
  induction lst with
  | nil => simp [GreedySelect]
  | cons x xs ih =>
    simp [GreedySelect]
    by_cases h : P (insert x (GreedySelect P xs).toFinset) = true
    · simpa [if_pos h]
    · simp [if_neg h, ih]

open List in
theorem GreedySelect.monotone {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
  {n : ℕ} (hn : n + 1 ≤ lst.length) : GreedySelect P (lst.rtake n) <+ GreedySelect P
  (lst.rtake (n + 1)) := by
  induction lst generalizing n with
  | nil => simp
  | cons x xs ih =>
    by_cases hn' : n + 1 = (x :: xs).length
    · rw [rtake_eq_reverse_take_reverse (x :: xs) (n + 1)]
      rw [take_of_length_le (by rw [length_reverse]; order), reverse_reverse]
      rw [rtake.eq_1, drop_cons (by rw [Nat.sub_pos_iff_lt]; exact Nat.lt_of_succ_le hn)]
      have : n = (x :: xs).length - 1 := by
        rwa [← Nat.Simproc.add_eq_le n ?_]
        exact Nat.one_le_of_lt hn
      rw [this]
      simp only [length_cons, add_tsub_cancel_right, add_tsub_cancel_left, tsub_self, drop_zero,
        GreedySelect]
      by_cases hP : P (insert x (GreedySelect P xs).toFinset)
      · rw [if_pos hP]
        exact sublist_cons_self x (GreedySelect P xs)
      · rw [if_neg hP]
    · have hn : n + 1 < (x :: xs).length := by exact Nat.lt_of_le_of_ne hn hn'
      rw [rtake.eq_1, drop_cons (by rw [Nat.sub_pos_iff_lt]; exact Nat.lt_of_succ_lt hn)]
      rw [rtake.eq_1, drop_cons (by rwa [Nat.sub_pos_iff_lt])]
      specialize ih (Nat.le_of_lt_succ hn)
      rw [rtake.eq_1, rtake.eq_1] at ih
      simp only [length_cons, Nat.reduceSubDiff]
      rwa [Nat.sub_sub xs.length n 1, Nat.sub_right_comm, Nat.add_one_sub_one]


open List in
theorem GreedySelect.chain {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
  {m n : ℕ} (hn : n ≤ lst.length) (hmn : m ≤ n) : GreedySelect P (lst.rtake m)
  <+ GreedySelect P (lst.rtake n) := by
  by_cases hmn' : m = n
  · rw [hmn']
  have h_len : lst.length ≠ 0 := by
    rw [Nat.le_iff_lt_or_eq] at hmn
    obtain h1 | h2 := hmn
    · have : 0 < n := by exact Nat.zero_lt_of_lt h1
      nth_rw 1 [Nat.ne_zero_iff_zero_lt]
      exact Nat.lt_of_lt_of_le this hn
    · contradiction
  have hmn'' : m < n := by exact Std.lt_of_le_of_ne hmn hmn'
  have : ∀ k : Fin (n - m + 1), GreedySelect P (lst.rtake ↑m) <+
    GreedySelect P (lst.rtake (↑m + ↑k)) := by
    intro k
    induction k using Fin.inductionOn with
    | zero => rfl
    | succ p ih =>
      by_cases hp : m + ↑p = lst.length
      · nth_rw 2 [rtake.eq_1] at ih ⊢
        rw [Fin.val_castSucc p] at ih
        rw [Nat.sub_eq_zero_of_le (by exact Nat.le_of_eq (id (Eq.symm hp)))] at ih
        rw [Nat.sub_eq_zero_of_le ?_]
        · exact ih
        rw [Fin.val_succ p, ← Nat.add_assoc m (↑p) 1]
        exact Nat.le.intro (congrFun (congrArg HAdd.hAdd (id (Eq.symm hp))) 1)
      trans
      · exact ih
      rw [Fin.val_castSucc, Fin.val_succ, ← add_assoc] at *
      apply GreedySelect.monotone
      have : m + ↑p < lst.length := by calc m + ↑p
        _ < m + (n - m) := by apply Nat.add_lt_add_left; exact (Fin.prop p)
        _ = n := by exact Nat.add_sub_of_le hmn
        _ ≤ lst.length := hn
      exact Order.add_one_le_iff.mpr this
  specialize this ⟨(n : ℕ) - ↑m, (by apply lt_add_one)⟩;
  simp [Nat.add_sub_of_le hmn] at this
  assumption

open List in
theorem GreedySelect.monotone' {α : Type*} [DecidableEq α] (P : Finset α → Bool) (x : α)
  (xs : List α) : GreedySelect P (x :: xs) <+ x :: (GreedySelect P xs) := by
  simp [GreedySelect]
  by_cases hP : P (insert x (GreedySelect P xs).toFinset)
  · simp [if_pos hP]
  · simp [if_neg hP]

open List in
theorem GreedySelect.sublist' {α : Type*} [DecidableEq α] (P : Finset α → Bool) (lst : List α)
  {n : ℕ} (hn : n + 1 ≤ lst.length) :
  GreedySelect P lst <+ lst.take (lst.length - n) ++ GreedySelect P (lst.rtake n) := by
  induction lst generalizing n with
  | nil => simp
  | cons x xs ih =>
    by_cases hn' : n + 1 = (x :: xs).length
    · have : (x :: xs).length - n = 1 := by
        rw [Nat.sub_eq_iff_eq_add' (Nat.le_of_succ_le hn), Eq.comm]; exact hn'
      rw [this, take.eq_3, take_zero]
      rw [rtake.eq_1, this, drop.eq_3, drop_zero]
      exact (GreedySelect.monotone' P x xs)
    · rw [rtake.eq_1, drop_cons (Nat.zero_lt_sub_of_lt hn)]
      rw [take_cons (Nat.zero_lt_sub_of_lt hn)]
      rw [length.eq_2, tsub_right_comm, Nat.add_one_sub_one]
      trans
      · exact GreedySelect.monotone' P x xs
      rw [cons_append, cons_sublist_cons]
      refine ih (?_)
      have : xs.length = (x :: xs).length - 1 := by rw [length_cons]; exact Nat.eq_sub_of_add_eq rfl
      rw [this, Nat.le_sub_one_iff_lt (by exact Nat.zero_lt_succ xs.length)]
      exact Nat.lt_of_le_of_ne hn hn'

#check List.Nodup

open List in
theorem GreedySelect.select_iff {α : Type*} [DecidableEq α] {P : Finset α → Bool} {lst : List α}
  {h_lst : List.Nodup lst} (n : Fin lst.length) : lst[n] ∈ GreedySelect P lst ↔
  P (insert lst[n] (GreedySelect P (lst.rtake (lst.length - n - 1))).toFinset) := by
  induction lst with
  | nil =>
    constructor
    · intro h
      rw [GreedySelect.eq_1, mem_nil_iff] at h
      contradiction
    · intro h
      simp at n
      cases n.isLt
  | cons x xs ih =>
    have h0 : 0 < (x :: xs).length := by rw [length_cons]; exact Nat.zero_lt_succ xs.length
    by_cases hxs : xs = []
    · have bla : n = ⟨0, h0⟩ := by
          rw [Fin.eq_mk_iff_val_eq]
          have := Fin.prop n
          nth_rw 2 [length_cons, hxs] at this
          rw [length_nil, Nat.zero_add] at this
          nth_rw 1 [← Nat.lt_one_iff]
          assumption
      have bli : [x].toFinset = {x} := by exact Finset.val_eq_singleton_iff.mp rfl
      constructor
      · intro h
        simp [GreedySelect, hxs] at h ⊢
        nth_rw 1 [← h.right] at bli
        rw [← bli] at h
        exact h.left
      · intro h
        simp [GreedySelect, hxs] at h ⊢
        have hn : ↑n < [x].length := by
          rw [length_singleton, bla, Nat.pos_iff_ne_zero]; exact Nat.one_ne_zero
        have h0' : 0 < [x].length := by rw [length_singleton]; exact Nat.one_pos
        have : ⟨n, hn⟩ = (⟨0, h0'⟩ : Fin [x].length) := by
          rw [Fin.mk_eq_mk]
          exact Fin.eq_mk_iff_val_eq.mp bla
        have : [x][n]'hn = x := by
          rw [show [x][n] = [x].get ⟨↑n, hn⟩ from rfl, this]
          rfl
        nth_rw 1 [← this]
        exact ⟨h, this⟩
    · by_cases hn : n = ⟨0, h0⟩
      · have : (x :: xs)[n] = x := by rw [hn]; rfl
        constructor
        · intro h
          rw [this] at h ⊢
          simp [GreedySelect] at h
          by_cases hP : P (insert x (GreedySelect P xs).toFinset)
          · rw [rtake.eq_1, hn]
            simp
            exact hP
          · rw [if_neg hP] at h
            have := GreedySelect.sublist P xs
            apply (List.Sublist.mem) at h
            specialize h this
            have := h_lst.notMem
            contradiction
        · intro h
          rw [this] at h ⊢
          have hn0 : (n : ℕ) = 0 := by exact Fin.eq_mk_iff_val_eq.mp hn
          rw [rtake.eq_1, Nat.sub_sub, Nat.sub_sub_self ?_] at h
          rw [hn0, Nat.zero_add, show drop 1 (x :: xs) = xs from rfl] at h
          simp [GreedySelect]
          rw [if_pos h]
          exact mem_cons_self
          rw [hn0, Nat.zero_add, length_cons]
          exact Nat.le_add_left 1 xs.length
      · have hn' : 0 < (n : ℕ) := by rw [Nat.pos_iff_ne_zero]; rw [Fin.eq_mk_iff_val_eq] at hn; exact hn
        have : 0 < xs.length := by rw [length_pos_iff]; exact hxs
        have h1 : 1 < (x :: xs).length := by rw [length_cons]; exact Nat.lt_add_of_pos_left this
        set k := n - ⟨1, h1⟩ with hk
        have hk' : k < xs.length := by
          rw [hk]
          rw [Fin.sub_val_of_le ?_]
          apply Nat.sub_one_lt_of_le hn'
          have := Fin.prop n
          nth_rw 2 [length_cons] at this
          exact Fin.is_le n
          rw [Fin.le_def, Nat.one_le_iff_ne_zero]
          exact Nat.ne_zero_of_lt hn'
        have hk'' : k + 1 < (x :: xs).length := by
          nth_rw 2 [length_cons]
          rwa [Nat.add_one_lt_add_one_iff]
        have hk''' : n = ⟨k.val + 1, hk''⟩ := by
          rw [Fin.ext_iff]
          rw [show ↑(⟨↑k + 1, hk''⟩ : Fin (x :: xs).length) = ↑k + 1 from rfl]
          rw [show k = n - ⟨1, h1⟩ from rfl]
          rw [Fin.sub_val_of_le (Fin.mk_le_of_le_val hn')]
          rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt hn')]
        have : (x :: xs).get ⟨k.val + 1, hk''⟩ = xs[k] := by rfl
        have bl: (x :: xs).get n = xs[k] := by rw [hk''']; exact this
        set l : Fin xs.length := ⟨k.val, hk'⟩ with hl
        have hl' : xs[l] = xs[k] := by
          rw [show xs[l] = xs.get ⟨↑l, hk'⟩ from rfl]
          rw [show xs[k] = xs.get ⟨↑k, hk'⟩ from rfl]
        have : xs.Nodup := by exact Nodup.of_cons h_lst
        specialize @ih this l
        constructor
        · intro h
          rw [show (x :: xs)[n] = (x :: xs).get n from rfl, bl] at h ⊢
          rw [← hl'] at h ⊢
          have : xs[l] ∈ x :: GreedySelect P xs := by
            apply Sublist.mem h
            exact (GreedySelect.monotone' P x xs)
          rw [mem_cons] at this
          obtain h_1 | h_2 := this
          · rw [nodup_cons] at h_lst
            have := h_lst.left
            rw [show (x ∉ xs) = (x ∈ xs → False) from rfl] at this
            have ha : xs[l] ∈ xs := by (expose_names; exact mem_of_getElem this_2)
            rw [h_1] at ha
            have := this ha
            contradiction
          · have ih := ih.mp h_2
            rw [rtake.eq_1] at ih ⊢
            rw [← Nat.Simproc.sub_add_eq_comm (x :: xs).length 1 ↑n]
            rw [tsub_tsub_cancel_of_le (Nat.one_add_le_iff.mpr n.isLt)]
            rw [drop_cons (Nat.add_pos_right 1 hn')]
            rw [Nat.one_add_sub_one ↑n]
            have : l.val + 1 = n.val := by rw [hk''']
            rw [Nat.sub_sub xs.length (↑l) 1] at ih
            rw [this] at ih
            rw [Nat.sub_sub_self (Fin.is_le n)] at ih
            exact ih
        · intro h
          rw [show (x :: xs)[n] = (x :: xs).get n from rfl, bl] at h ⊢
          rw [← hl'] at h ⊢
          rw [rtake.eq_1] at ih h
          rw [← Nat.Simproc.sub_add_eq_comm (x :: xs).length 1 ↑n] at h
          rw [tsub_tsub_cancel_of_le (Nat.one_add_le_iff.mpr n.isLt)] at h
          rw [drop_cons (Nat.add_pos_right 1 hn')] at h
          rw [Nat.one_add_sub_one ↑n] at h
          rw [Nat.sub_sub xs.length (↑l) 1] at ih
          rw [Nat.sub_sub_self (Order.add_one_le_iff.mpr hk')] at ih
          rw [Fin.sub_val_of_le (Fin.mk_le_of_le_val hn')] at ih
          rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt hn')] at ih
          have ih := ih.mpr h
          apply Sublist.mem ih
          simp [GreedySelect]
          by_cases hP' : P (insert x (GreedySelect P xs).toFinset)
          · rw [if_pos hP']
            exact sublist_cons_self x (GreedySelect P xs)
          · rw [if_neg hP']

namespace GreedySelectExample

def P : Finset (Fin 3) → Bool := fun X ↦ match X.card with
| 0 => true
| 1 => true
| 2 => true
| _ => false

def lst : List (Fin 3) := [3, 2, 1]

#eval GreedySelect P lst

end GreedySelectExample

open Classical in
noncomputable def GreedyMin {α β : Type*} [DecidableEq α] [LinearOrder β] (F : IndepSystem α)
  (c : α → β) : List α :=
  GreedySelect F.Indep (F.E.toList.mergeSort (fun a b ↦ decide (c a ≤ c b)))

lemma LE_lift {α β : Type*} [LinearOrder β] (lst : List α) (c : α → β) :
  ((lst.mergeSort (fun a b ↦ decide (c a ≤ c b))).map c).SortedLE := by
  let r (a b : α) : Prop := c a ≤ c b
  let h_total : IsTotal α r := ⟨fun a b ↦ le_total (c a) (c b)⟩
  let h_trans : IsTrans α r := ⟨fun a b d ha hb ↦ le_trans ha hb⟩
  have h' : ∀ a b, r a b → c a ≤ c b := by intro a b hrab; unfold r at hrab; assumption
  have := (List.pairwise_mergeSort' r lst).map c h'
  exact List.Pairwise.sortedLE this

#check List.Pairwise.sublist
#check List.isChain_map

theorem GreedyMin.sorted {α β : Type*} [DecidableEq α] [LinearOrder β] {F : IndepSystem α}
  {c : α → β} : ((GreedyMin F c).map c).SortedLE := by
  let r (a b : α) : Prop := c a ≤ c b
  let h_total : IsTotal α r := ⟨fun a b ↦ le_total (c a) (c b)⟩
  let h_trans : IsTrans α r := ⟨fun a b d ha hb ↦ le_trans ha hb⟩
  have := LE_lift F.E.toList c
  unfold GreedyMin
  rw [List.sortedLE_iff_isChain, List.isChain_map] at *
  rw [List.isChain_iff_pairwise] at *
  refine List.Pairwise.sublist (?_) this
  exact GreedySelect.sublist F.Indep (F.E.toList.mergeSort fun a b ↦ decide (c a ≤ c b))
