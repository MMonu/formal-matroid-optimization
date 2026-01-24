import Mathlib.Tactic

import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.FinMatroid.FinBases
import FormalMatroidOptimization.Greedy.Basic
import FormalMatroidOptimization.List.Greedy
import Mathlib.Order.Minimal

namespace FinMatroid

noncomputable def selectRel {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) [DecidablePred F.Indep] :
    List α := Greedy.selectRel F.Indep r F.E.toList

noncomputable def selectRel' {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) [DecidablePred F.Indep] :
    List α := List.Greedy.selectRel F.Indep r F.E.toList

def weight {α β : Type*} [AddCommMonoid β] (c : α → β) (X : Finset α) : β := Finset.sum X c

lemma weight_of_union {α β : Type*} [DecidableEq α] [AddCommMonoid β] (c : α → β) {X Y : Finset α}
    (h : Disjoint X Y) : weight c (X ∪ Y) = weight c X + weight c Y := by
  simp [weight, Finset.sum_union h]

lemma weight_pos_of_pos {α β : Type*} [DecidableEq α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddMonoid β] {c : α → β} (h : ∀ a, 0 ≤ c a) {X : Finset α} : 0 ≤ weight c X := by
  refine Finset.induction_on X ?_ ?_
  · simp [weight]
  · intro y Y hyY ih
    rw [weight, Finset.sum_insert hyY]
    have := add_le_add (h y) ih
    rwa [zero_add, weight] at this

lemma weight_monotone_of_pos {α β : Type*} [DecidableEq α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddMonoid β] {c : α → β} (h : ∀ a, 0 ≤ c a) {X Y : Finset α} :
    weight c X ≤ weight c (X ∪ Y) := by
  nth_rw 1 [← Finset.union_sdiff_self_eq_union, weight_of_union, ← add_zero (weight c X)]
  · exact add_le_add (by simp) (weight_pos_of_pos h)
  · exact Finset.disjoint_sdiff

def is_min_weight_base {α β : Type*} [DecidableEq α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddMonoid β] (F : IndepSystem α) (c : α → β) (B : Finset α) : Prop :=
    IsFinBase F B ∧ ∀ B', IsFinBase F B' → weight c B' ≤ weight c B

def weightRel {α β : Type*} [LinearOrder β] (c : α → β) := Order.Preimage c (· ≤ ·)

noncomputable instance {α : Type*} (E : Finset α) : Encodable {x // x ∈ E} := Fintype.toEncodable E

open Encodable in
def rel_of_encodable_of_rel {α : Type*} [Encodable α] (r : α → α → Prop) : α → α → Prop :=
  fun a b ↦ r a b ∧ (r b a → encode a ≤ encode b)

instance instTrans {α : Type*} [Encodable α] (r : α → α → Prop) [IsTrans α r] :
    IsTrans α (rel_of_encodable_of_rel r) where
  trans := by
    intro a b c ⟨hab₁, hab₂⟩ ⟨hbc₁, hbc₂⟩
    simp only [rel_of_encodable_of_rel]
    refine ⟨trans_of r hab₁ hbc₁, ?_⟩
    intro hca
    exact le_trans (hab₂ (trans_of r hbc₁ hca)) (hbc₂ (trans_of r hca hab₁))

open Encodable in
instance instTotal {α : Type*} [Encodable α] (r : α → α → Prop) [IsTotal α r] :
    IsTotal α (rel_of_encodable_of_rel r) where
  total := by
    intro a b
    simp only [rel_of_encodable_of_rel]
    by_cases h : encode a ≤ encode b
    · by_cases hab : r a b
      · left; exact ⟨hab, fun _ ↦ h⟩
      · right; refine ⟨(or_iff_right hab).mp (total_of r a b), by intro hab'; contradiction⟩
    · have h := le_of_lt (not_le.mp h)
      by_cases hba : r b a
      · right; exact ⟨hba, fun _ ↦ h⟩
      · left; refine ⟨(or_iff_right hba).mp (total_of r b a), by intro hba'; contradiction⟩

open Encodable in
instance instAntisymm {α : Type*} [Encodable α] (r : α → α → Prop) :
    IsAntisymm α (rel_of_encodable_of_rel r) where
  antisymm := by
    intro a b ⟨hab₁, hab₂⟩ ⟨hba₁, hba₂⟩
    exact encode_inj.mp (eq_of_le_of_ge (hab₂ hba₁) (hba₂ hab₁))

noncomputable instance instDecidableRel {α : Type*} [Encodable α] (r : α → α → Prop)
    [DecidableRel r] : DecidableRel (rel_of_encodable_of_rel r) := by
  unfold rel_of_encodable_of_rel; infer_instance

def weightRel' {α β : Type*} [Encodable α] [LinearOrder β] (c : α → β) :=
    rel_of_encodable_of_rel (Order.Preimage c (· ≤ ·))

@[simp]
lemma weightRel'_of_weight_lt {α β : Type*} [Encodable α] [LinearOrder β] (c : α → β) {a b : α}
    (h : c a < c b) : (weightRel' c) a b := by
  simp only [weightRel', rel_of_encodable_of_rel, Order.Preimage]
  refine ⟨le_of_lt h, by intro hc; order⟩

instance weight_instTrans {α β : Type*} [Encodable α] [LinearOrder β] (c : α → β) :
    IsTotal α (weightRel' c)
  := by unfold weightRel'; infer_instance

instance weight_instTotal {α β : Type*} [Encodable α] [LinearOrder β] (c : α → β) :
    IsTrans α (weightRel' c)
  := by unfold weightRel'; infer_instance

instance weight_instAntisymm {α β : Type*} [Encodable α] [LinearOrder β] (c : α → β) :
    IsAntisymm α (weightRel' c)
  := by unfold weightRel'; infer_instance

noncomputable instance weight_instDecidableRel {α β : Type*} [Encodable α] [LinearOrder β]
    (c : α → β) : DecidableRel (weightRel' c)
  := by unfold weightRel'; infer_instance

noncomputable section

instance {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] (c : α → β) :
    DecidableRel (weightRel c) := Classical.decRel (weightRel c)
end

local instance {α : Type*} [Encodable α] : DecidableEq α := Encodable.decidableEqOfEncodable α
instance {α : Type*} {F : IndepSystem α} : DecidablePred F.Indep := F.indep_dec

noncomputable def greedy {α β : Type*} [Encodable α] [LinearOrder β] (F : IndepSystem α)
    (c : α → β) : List α :=
  Greedy.selectRel F.Indep (weightRel' c) F.E.toList

lemma greedy_eq {α β : Type*} [Encodable α] [LinearOrder β] (F : IndepSystem α) (c : α → β) :
    greedy F c = List.Greedy.selectRel F.Indep (weightRel' c) F.E.toList := by
  rw [greedy, Greedy.selectRel_eq_list_selectRel F.indep_subset (weightRel' c) ?_ ?_]
  · exact Finset.nodup_toList F.E
  · intro x y hx hy ⟨h₁, h₂⟩
    exact antisymm h₁ h₂

open Finset in
lemma greedy_IsFinBase {α β : Type*} [Encodable α] [LinearOrder β] (F : IndepSystem α) (c : α → β) :
    IsFinBase F (greedy F c).toFinset := by
  rw [IsFinBase, greedy, Greedy.selectRel, maximal_iff_forall_gt]
  refine ⟨Greedy.selectRel_internal_indep (F.indep_empty), ?_⟩
  intro I hleI hI
  obtain ⟨x, hx₁, hx₂⟩ := ssubset_iff.mp (lt_iff_ssubset.mp hleI)
  refine Greedy.selectRel_internal_maximal x ?_ hx₁ (F.indep_subset hI hx₂)
  simp [(F.subset_ground hI) (insert_subset_iff.mp hx₂).left]

/-
lemma Greedy_maxweight {α : Type*} [DecidableEq α] (M : FinMatroid α) [DecidablePred M.Indep]
  (B : Finset α) (hB: IsFinBase M B) (c : α → ℝ) :
  ∀ i ∈ [B.card],
  c ((B.toList.mergeSort (fun a b ↦ weightRel c a b))[i]!) ≤
    c ((Greedy_set M c).toList[i]!) := by sorry
-/

-- theorem Matroid_then_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
--   IsFinMatroid F →
--   ∀ c : α → β ,
--       Maximal F.Indep (Greedy_set F c) ∧
--       weight_is_maximum F c (Greedy_set F c) := by
--   intro h c
--   constructor
--   · have : ∀ ⦃s t : Finset α⦄, F.Indep t → s ⊆ t → F.Indep s := by
--       intro X Y hX
--       apply F.indep_subset
--       grind only
--     rw [Finset.maximal_iff_forall_insert (P := F.Indep) this]
--     constructor
--     · -- indep
--       have : F.Indep ([].toFinset) := by simp only [List.toFinset_nil, F.indep_empty]
--       have := Greedy.selectRel_internal_indep
--         (P := F.Indep) (r := weightRel c) (xs := F.E.toList) (ys := []) this
--       exact ((fun a ↦ this) ∘ fun a ↦ α) α
--     · -- max
--       intro x hxnot
--       by_cases hx : x ∈ F.E.toList
--       · exact Greedy.selectRel_internal_maximal
--           (P := F.Indep) (r := weightRel c) (xs := F.E.toList) (ys := []) x hx hxnot
--       · intro hxInd
--         have hxSubset : insert x (Greedy_set F c) ⊆ F.E := F.subset_ground hxInd
--         have : x ∈ F.E := hxSubset (by simp)
--         have : x ∈ F.E.toList := Finset.mem_toList.mpr this
--         contradiction
--   · -- max weight
--     unfold weight_is_maximum
--     intro X hX
--     unfold IsFinMatroid at h
--     set M := IndepToMatroidUp (F := F) (h := h) with hM
--     have : F.Indep = M.Indep := Set.setOf_inj.mp rfl
--     rw [this] at hX
--     set GB := Greedy_set F c with hGB
--     unfold Greedy_set at hGB
--     unfold selectRel at hGB
--     have hxs : (F.E.toList).Nodup := by sorry
--     have ha : ∀ (x y : α), x ∈ F.E.toList → y ∈ F.E.toList →
--         weightRel c x y ∧ weightRel c y x → x = y := by
--       intro x y hx hy
--       unfold weightRel
--       --exact le_antisymm_iff.mpr (c x) (c y)
--       sorry
--     rw [Greedy.selectRel_eq_list_selectRel (P:= F.Indep) (F.indep_subset)
--       (r := weightRel c) (hxs) (ha)] at hGB
--     --mergeSort_toFinset_eq
--     sorry

open Finset in
lemma exists_eq_insert_of_card_succ {α : Type*} [DecidableEq α] {X Y : Finset α} (hXY : X ⊆ Y)
    (hcard : #Y = #X + 1) : ∃ x, x ∈ Y ∧ x ∉ X ∧ Y = insert x X:= by
  have h : (Y \ X).card = 1 := by grind
  obtain ⟨x, hx⟩ := card_eq_one.mp h
  use x
  have hx' := (mem_sdiff.mp (eq_singleton_iff_unique_mem.mp hx).left)
  refine ⟨hx'.left, hx'.right, ?_⟩
  ext y
  constructor
  · intro h
    rw [mem_insert]
    rw [← sdiff_union_inter Y X, mem_union] at h
    cases h with
    | inl h' => simp only [hx, mem_singleton] at h'; left; exact h'
    | inr h' => right; grind
  · intro h
    rw [mem_insert] at h
    cases h with
    | inl h' => rw [h']; exact hx'.left
    | inr h' => exact hXY h'

open Finset List Encodable in
theorem Matroid_of_greedy {α : Type*} [Encodable α] (F : IndepSystem α)
    (h : ∀ {β : Type}, [LinearOrder β] → [AddCommMonoid β] → [IsOrderedAddMonoid β] →
      ∀ c : α → β, is_min_weight_base F c (greedy F c).toFinset) : IsFinMatroid F := by
  apply IndepSystem.augmentation_of_succ _ F.indep_subset
  intro Y X hY hX h_card
  by_cases hXY₁ : X \ Y = ∅
  · obtain ⟨x, hx⟩ := exists_eq_insert_of_card_succ (sdiff_eq_empty_iff_subset.mp hXY₁) h_card
    refine ⟨x, hx.left, hx.right.left, by rwa [← hx.right.right]⟩
  · set u : ℕ := #(X \ Y) + #(Y \ X) with hu
    set v : ℕ := 2 * #(X \ Y) with hv
    set c : α → ℕ := fun x ↦ if x ∈ X then u else (if x ∈ Y then v else 0)
    have h0v : 0 < v := by grind only [= card_sdiff, usr card_ne_zero_of_mem, ← notMem_empty]
    have huv : v < u := by grind only [usr card_sdiff_add_card_inter, usr card_union_add_card_inter]
    have hX₁ : X = (X \ Y) ∪ (X ∩ Y) := (sdiff_union_inter X Y).symm
    have hX₂ : Disjoint (X \ Y) (X ∩ Y) := disjoint_sdiff_inter X Y
    have hX₃ : #X ≤ #F.E := card_le_card (F.subset_ground hX)
    have hY₁ : Y = (Y \ X) ∪ (X ∩ Y) := by nth_rw 1 [← sdiff_union_inter Y X, inter_comm]
    have hY₂ : Disjoint (Y \ X) (X ∩ Y) := by rw [inter_comm]; exact disjoint_sdiff_inter Y X
    have hXY₂ : #(X \ Y) < #(Y \ X) := by rw [card_sdiff_lt_card_sdiff_iff]; simp [h_card]
    have hwX : weight c X = #X * u := by simp [weight, c, sum_ite_of_true]
    have hwY : weight c Y = #(Y \ X) * v + #(X ∩ Y) * u := by
      nth_rw 1 [hY₁, weight_of_union c hY₂]
      simp only [weight, c]
      rw [sum_ite_of_false <| by simp, sum_ite_of_true <| by grind, sum_ite_of_true <| by grind]
      simp
    have hw₁ : weight c X < weight c Y := by
      nth_rw 1 [hwX, hwY, hX₁, card_union_of_disjoint hX₂, add_mul, add_lt_add_iff_right]
      simp only [u, v]
      rw [two_mul, mul_add, mul_add, mul_comm #(Y \ X) #(X \ Y), add_lt_add_iff_right]
      rwa [mul_lt_mul_iff_right₀ <| card_pos.mpr (nonempty_iff_ne_empty.mpr hXY₁)]
    --
    by_contra hc
    simp only [not_exists, not_and] at hc
    set lg := (F.E.toList.mergeSort fun x y ↦ decide (weightRel' c x y)) with hlg
    set lX := X.sort (weightRel' c) with hlX
    set lY := (Y \ X).sort (weightRel' c) with hlY
    set lC := (F.E \ (X ∪ Y)).sort (weightRel' c) with hlC
    have hlg₁ : greedy F c = List.Greedy.select F.Indep lg := by
      rw [greedy_eq, List.Greedy.selectRel, hlg]
    have hlg_part : lC ++ lY ++ lX = lg := by
      have hls : (lC ++ lY ++ lX).Pairwise (weightRel' c) := by
        have h₁ : ∀ {a}, a ∈ lX → c a = u := by intro a ha; grind [(mem_sort _).mp ha]
        have h₂ : ∀ {a}, a ∈ lY → c a = v := by intro a ha; grind [(mem_sort _).mp ha]
        have h₃ : ∀ {a}, a ∈ lC → c a = 0 := by intro a ha; grind [(mem_sort _).mp ha]
        rw [hlC, hlY, hlX, pairwise_append, pairwise_append]
        refine ⟨?_, pairwise_sort _ _, ?_⟩
        · refine ⟨pairwise_sort _ _, pairwise_sort _ _, ?_⟩
          intro a ha b hb
          exact weightRel'_of_weight_lt c <| by rwa [h₃ ha, h₂ hb]
        · intro a ha b hb
          cases mem_append.mp ha with
          | inl hac =>
            exact weightRel'_of_weight_lt c <| by rw [h₃ hac, h₁ hb]; exact Nat.zero_lt_of_lt huv
          | inr hac => exact weightRel'_of_weight_lt c <| by rwa [h₂ hac, h₁ hb]
      refine List.Perm.eq_of_pairwise' hls (pairwise_mergeSort' _ _) ?_
      refine (perm_ext_iff_of_nodup ?_ ?_).mpr ?_
      · rw [hlX, hlY, hlC, nodup_append', nodup_append']
        refine ⟨?_, sort_nodup _ _, ?_⟩
        · refine ⟨sort_nodup _ _, sort_nodup _ _, ?_⟩
          intro a ha
          rw [mem_sort _] at ha ⊢
          grind only [= mem_sdiff, = mem_union]
        · intro a ha
          rw [mem_append, mem_sort _, mem_sort] at ha
          cases ha with
          | inl hac => rw [mem_sort _]; grind only [= mem_sdiff, = mem_union, = mem_inter]
          | inr hac => rw [mem_sort _]; grind only [= mem_sdiff]
      · exact nodup_mergeSort.mpr (nodup_toList F.E)
      · intro a
        rw [mem_append, mem_append, mem_sort _, mem_sort _, mem_sort _, mem_mergeSort, mem_toList]
        rw [← mem_union, ← mem_union, union_assoc, sdiff_union_self_eq_union, union_comm X Y]
        rw [sdiff_union_of_subset ?_]
        exact union_subset_iff.mpr ⟨F.subset_ground hY, F.subset_ground hX⟩
    --
    have hlX₁ : ∀ l, l <+ lX → List.Greedy.select F.Indep l = l := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        specialize ih (sublist_of_cons_sublist hl)
        rw [List.Greedy.select_cons_pos ?_, ih]
        refine F.indep_subset hX ?_
        intro z hz
        rw [ih, ← toFinset_cons, mem_toFinset] at hz
        exact (mem_sort _).mp (Sublist.mem hz hl)
    have hlY₁ : ∀ l, l <+ lY → List.Greedy.select F.Indep (l ++ lX) = lX := by
      intro l hl
      induction l with
      | nil => simp [hlX₁]
      | cons x xs ih =>
        rw [cons_append, Greedy.select_cons_neg ?_, ih (sublist_of_cons_sublist hl)]
        rw [ih (sublist_of_cons_sublist hl), sort_toFinset]
        refine hc x ?_ ?_
        <;> simp [(mem_sdiff.mp ((mem_sort _).mp (mem_of_cons_sublist hl)))]
    set lB := (List.Greedy.select F.Indep lg) with hlB
    have hlB₁ : lX ⊆ lB := by
      refine Sublist.subset ?_
      rw [← hlX₁ lX (by simp), hlB, ← hlg_part]
      exact List.Greedy.select_monotone' _ lX
    have hlB₂ : lB ⊆ lX ∪ lC := by
      trans
      · refine Sublist.subset (l₂ := lC ++ lX) ?_
        rw [← hlY₁ lY (by simp), hlB, ← hlg_part, append_assoc]
        refine List.Greedy.select_append_sublist (P := F.Indep)
      · grind only [= List.subset_def, = mem_union_iff, = mem_append]
    obtain ⟨B', hB'₁, hB'₂⟩ := exists_IsFinBase_superset hY
    --
    have hwB : weight c lB.toFinset = weight c X := by
      rw [hwX, weight, ← sdiff_union_inter lB.toFinset X, sum_union (disjoint_sdiff_inter _ _)]
      rw [sum_ite_of_false (by simp), sum_ite_of_false ?_, sum_const_zero]
      · rw [inter_eq_right.mpr ?_, sum_ite_of_true (by simp), sum_const, zero_add]
        · simp
        · intro x hx
          exact mem_toFinset.mpr (hlB₁ ((mem_sort (weightRel' c)).mpr hx))
      · intro x hx
        obtain ⟨hx₁, hx₂⟩ := mem_sdiff.mp hx
        cases mem_union_iff.mp (hlB₂ (mem_toFinset.mp hx₁)) with
        | inl hx₃ => exact False.elim (hx₂ ((mem_sort _).mp hx₃))
        | inr hx₃ => rw [mem_sort _] at hx₃; grind
    have hwB' : weight c Y ≤ weight c B' := by
      rw [← sdiff_union_inter B' Y, inter_comm, inter_eq_left.mpr hB'₂, union_comm]
      refine weight_monotone_of_pos (c := c) ?_
      grind

    exact (lt_self_iff_false _).mp (calc weight c (greedy F c).toFinset
    _ = weight c X := by rw [hlg₁, hwB]
    _ < weight c Y := hw₁
    _ ≤ weight c B' := hwB'
    _ ≤ weight c (greedy F c).toFinset := (h c).right B' hB'₁)

-- theorem Matroid_iff_Greedy {α : Type*} [DecidableEq α] (F : IndepSystem α) [DecidablePred F.Indep] :
--   IsFinMatroid F ↔
--   ∀ c : α → ℝ,
--       Maximal F.Indep (Greedy_set F c) ∧
--       weight_is_maximum F c (Greedy_set F c) := by
--   sorry

end FinMatroid
