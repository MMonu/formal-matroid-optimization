import Mathlib.Tactic

import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.FinMatroid.FinBases
import FormalMatroidOptimization.FinMatroid.FinCircuit
import FormalMatroidOptimization.Greedy.Basic
import FormalMatroidOptimization.List.Greedy
import FormalMatroidOptimization.Weight
import Mathlib.Order.Minimal

open List Finset Encodable

namespace FinMatroid

local instance {α : Type*} [Encodable α] : DecidableEq α := Encodable.decidableEqOfEncodable α

noncomputable def selectRel {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) [DecidablePred F.Indep] :
    List α := Greedy.selectRel F.Indep r F.E.toList

def is_max_weight_base {α β : Type*} [DecidableEq α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] (F : IndepSystem α) (c : α → β) (B : Finset α) : Prop :=
    IsFinBase F B ∧ ∀ B', IsFinBase F B' → weight c B' ≤ weight c B

lemma is_max_weight_base_eq {α β : Type*} [DecidableEq α] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] {c : α → β} {F : IndepSystem α} (I : Finset α) :
    (∀ B', IsFinBase F B' → weight c B' ≤ weight c I) ↔
    (F.E.powerset.filter (fun J ↦ IsFinBase F J ∧ weight c J > weight c I) = ∅) := by
  rw [filter_eq_empty_iff]
  refine ⟨?_, ?_⟩
  · intro h J hJ
    rw [not_and, not_lt]
    intro hJ₁
    exact h _ hJ₁
  · intro h J hJ
    have h := h (mem_powerset.mpr (F.subset_ground hJ.left))
    rw [not_and, not_lt] at h
    exact h hJ

instance {α β : Type*} [DecidableEq α] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] {c : α → β} {F : IndepSystem α} :
    DecidablePred (is_max_weight_base F c) := by
  intro I
  rw [is_max_weight_base, is_max_weight_base_eq]
  infer_instance

noncomputable def greedy {α β : Type*} [Encodable α] [LinearOrder β] (F : IndepSystem α)
    (c : α → β) : List α :=
  Greedy.selectRel F.Indep (weightRel' c) F.E.toList

lemma greedy_eq {α β : Type*} [Encodable α] [LinearOrder β] (F : IndepSystem α) (c : α → β) :
    greedy F c = List.Greedy.selectRel F.Indep (weightRel' c) F.E.toList := by
  rw [greedy, Greedy.selectRel_eq_list_selectRel F.indep_subset (weightRel' c) ?_ ?_]
  · exact nodup_toList F.E
  · intro x y hx hy ⟨h₁, h₂⟩
    exact antisymm h₁ h₂

lemma greedy_IsFinBase {α β : Type*} [Encodable α] [LinearOrder β] (F : IndepSystem α) (c : α → β) :
    IsFinBase F (greedy F c).toFinset := by
  rw [IsFinBase, greedy, Greedy.selectRel, maximal_iff_forall_gt]
  refine ⟨Greedy.selectRel_internal_indep (F.indep_empty), ?_⟩
  intro I hleI hI
  obtain ⟨x, hx₁, hx₂⟩ := ssubset_iff.mp (lt_iff_ssubset.mp hleI)
  refine Greedy.selectRel_internal_maximal x ?_ hx₁ (F.indep_subset hI hx₂)
  simp only [mem_toList, (F.subset_ground hI) (insert_subset_iff.mp hx₂).left]

lemma FinBases_notsub {α : Type*} [DecidableEq α] {M : FinMatroid α} {X X' : Finset α}
    (hX : IsFinBase M X) (hX' : IsFinBase M X') (hneq : X ≠ X') : ∃ x, x ∈ X \ X' := by
  have hnX : ¬ X ⊆ X' := by
    by_contra
    have := Finset.Subset.antisymm this ((le_iff_subset).mp (hX.2 hX'.1 this))
    contradiction
  refine nonempty_def.mp ?_
  exact sdiff_nonempty.mpr hnX

lemma FinDep_exists_FinCircuit_subset {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {X : Finset α} (hX : FinDep M X) : ∃ C ⊆ X, IsFinCircuit M C :=
  exists_minimal_le_of_wellFoundedLT (FinDep M) X hX

lemma FinCircuit_ex_mem_nin_FinBase {α : Type*} [DecidableEq α] {M : FinMatroid α} {B C : Finset α}
    (hB : IsFinBase M B) (hC : IsFinCircuit M C) : ∃ e, e ∈ C \ B := by
  by_contra
  have : C ⊆ B := by simp_all; grind
  grind only [FinDep, M.indep_subset hB.1, hC.1]

lemma FinBase_mem_insert_circuit_mem {α : Type*} [DecidableEq α] {M : FinMatroid α} {e : α}
    {B C : Finset α} (hB : IsFinBase M B) (hC : IsFinCircuit M C) (hCB : C ⊆ (insert e B)) :
    e ∈ C \ B := by
  grind only [FinDep, subset_iff, insert_eq_of_mem, mem_sdiff, mem_insert,
    M.indep_subset hB.1, hC.1]

lemma FinBase_mem_insert_circuit {α : Type*} [DecidableEq α] {M : FinMatroid α} {e : α}
    {B : Finset α} (hB : IsFinBase M B) (he : e ∈ M.E \ B) :
    ∃ C ⊆ (insert e B), IsFinCircuit M C ∧ e ∈ C \ B := by
  have he' : e ∈ M.toMatroid.E \ B := by
    rw [Set.mem_diff]
    rwa [mem_sdiff] at he
  have hBe_dep : FinDep M (insert e B) := by
    refine (FinDep_iff_Dep M (insert e B)).mpr ?_
    rw [coe_insert]
    exact Matroid.IsBase.insert_dep ((IsFinBase_iff_IsBase M B).mp hB) he'
  grind only [FinBase_mem_insert_circuit_mem, FinDep_exists_FinCircuit_subset hBe_dep]

lemma FinCircuit_ex_mem_nin_Indep {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {I C : Finset α} (hI : M.Indep I) (hC : IsFinCircuit M C) : ∃ c, c ∈ C \ I := by
  by_contra!
  simp only [mem_sdiff, not_and, Decidable.not_not, ← subset_iff] at this
  grind only [FinDep, M.indep_subset hI this, hC.1]

lemma FinIndep_exchange_mem_circuit_FinIndep {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {e f : α} {I C : Finset α} (hI : M.Indep I) (hC : IsFinCircuit M C) (heI : e ∈ C \ I)
    (hCe : C ⊆ (insert e I)) (hf : f ∈ C \ {e}) : M.Indep (insert e I \ {f}) := by
  refine (FinIndep_iff_Indep M (insert e I \ {f})).mpr ?_
  have he_cl : e ∈ M.toMatroid.closure I := by
    refine (Matroid.Indep.mem_closure_iff ((FinIndep_iff_Indep M I).mp hI)).mpr ?_
    left
    simpa [coe_insert] using ((FinDep_iff_Dep M (insert e I)).mp (by
      constructor
      · by_contra; grind only [FinDep, M.indep_subset this hCe, hC.1]
      · rw [insert_eq e I]
        refine union_subset ?_ (M.subset_ground hI)
        grind only [mem_sdiff, hC.1.2, subset_iff, singleton_subset_iff]))
  rw [mem_sdiff] at heI hf
  have := Matroid.IsCircuit.eq_fundCircuit_of_subset ((FinCircuit_iff_Circuit M C).mp hC)
    ((FinIndep_iff_Indep M I).mp hI) (by rwa [← coe_subset, coe_insert e I] at hCe)
  rw [coe_sdiff, coe_insert, coe_singleton]
  exact ((Matroid.Indep.mem_fundCircuit_iff ((FinIndep_iff_Indep M I).mp hI)) he_cl heI.2).mp
    (by rw [← mem_coe, this] at hf; exact hf.1)

lemma FinBase_exchange_mem_circuit_Finbase {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {b e : α} {B C : Finset α} (hB : IsFinBase M B) (hC : IsFinCircuit M C) (heB : e ∈ C \ B)
    (hCe : C ⊆ (insert e B)) (hb : b ∈ C \ {e}) : IsFinBase M (insert e B \ {b}) := by
  have hI := FinIndep_exchange_mem_circuit_FinIndep (f := b) (I := B) (hB.1) (hC) (heB) (hCe) (hb)
  have hI' := by simpa [coe_sdiff, coe_insert, coe_singleton] using
    ((FinIndep_iff_Indep M (insert e B \ {b})).mp hI)
  have := Matroid.IsBase.exchange_isBase_of_indep' (M := M.toMatroid)
    ((IsFinBase_iff_IsBase M B).mp hB) (by grind) (by grind) hI'
  rw [← coe_insert, ← coe_singleton, ← coe_sdiff] at this
  exact (IsFinBase_iff_IsBase M (insert e B \ {b})).mpr this

lemma greedy_exists_T {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] {M : FinMatroid α} {c : α → β} {A : Finset α}
    (hex : ∃ X, IsFinBase M X ∧ weight c A < weight c X) :
    ∃ B, IsFinBase M B ∧
        (is_max_weight_base M c B) ∧
        (weight c A < weight c B) ∧
        (∀ X, IsFinBase M X ∧ weight c X = weight c B → (X ∩ A).card ≤ (B ∩ A).card) := by
  set sT' := M.E.powerset.filter (fun X ↦ IsFinBase M X ∧ weight c A < weight c X) with hsT'
  have := exists_max_image sT' (fun X ↦ weight c X) (by
    obtain ⟨X, hXb, hXw⟩ := hex
    use X
    grind [M.subset_ground hXb.1])
  obtain ⟨C, hC, hC_maxw⟩ := this
  set sT := sT'.filter (fun X ↦ weight c X = weight c C) with hsT
  have := exists_max_image sT (fun X : Finset α ↦ (X ∩ A).card) (by
    use C
    grind only [Finset.mem_filter])
  obtain ⟨T, hT, hT_int⟩ := this
  rw [hsT, Finset.mem_filter] at hT
  obtain ⟨hT', hT_maxw'⟩ := hT
  simp only [hsT', Finset.mem_filter, mem_powerset] at hT'
  obtain ⟨hT_sub, hT_base, hT_weight⟩ := hT'
  have hT_maxw : is_max_weight_base M c T := by
    refine ⟨hT_base, ?_⟩
    intro B hB
    by_cases hBsT' : B ∈ sT'
    · simp_all [hC_maxw B hBsT']
    · simp only [hsT', Finset.mem_filter, mem_powerset, not_and, not_lt] at hBsT'
      grind [hBsT' (M.subset_ground hB.1) hB]
  use T
  refine ⟨hT_base, ⟨hT_maxw, ⟨hT_weight, ?_⟩⟩⟩
  intro X ⟨hX1, hX2⟩
  have : X ∈ sT := by
    rw [hsT, Finset.mem_filter]
    rw [hT_maxw'] at hX2
    refine ⟨?_, hX2⟩
    rw [hsT', Finset.mem_filter, mem_powerset]
    rw [hT_maxw', ← hX2] at hT_weight
    refine ⟨M.subset_ground hX1.1, ⟨hX1, hT_weight⟩⟩
  exact String.Pos.Raw.mk_le_mk.mp (hT_int X this)

lemma FinBase_maxweight_no_change {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] {M : FinMatroid α} {c : α → β} {B C : Finset α} {b e : α}
    (hB : IsFinBase M B) (hm : is_max_weight_base M c B) (heB : e ∈ C \ B) (hC : IsFinCircuit M C)
    (hCe : C ⊆ (insert e B)) (hb : b ∈ C \ {e}) : c e ≤ c b := by
  by_contra!
  have : weight c B < weight c (insert e B \ {b}) := by
    have h₁ : {b} ⊆ B := by grind only [mem_sdiff, subset_iff, singleton_subset_iff,
      Finset.mem_singleton, mem_insert]
    have h₂ : Disjoint (B \ {b}) {b} := sdiff_disjoint
    have h₃ : Disjoint {e} (B \ {b}) := by simp_all
    have h₄ : e ≠ b := by grind only
    calc weight c B = weight c ((B \ {b}) ∪ {b}) := by simp_all
                  _ = weight c {b} + weight c (B \ {b}) := by grind [weight_of_union]
                  _ = c b + weight c (B \ {b}) := by grind only [weight, sum_singleton']
                  _ < c e + weight c (B \ {b}) := by simp_all [add_lt_add_iff_right]
                  _ = weight c {e} + weight c (B \ {b}) := by grind [weight]
                  _ = weight c ({e} ∪ (B \ {b})) := by grind only [weight_of_union]
                  _ = weight c (insert e B \ {b}) := ?_
    · rw [singleton_union e (B \ {b}), ← insert_sdiff_of_notMem B ?_]
      exact notMem_singleton.mpr h₄
  grind only [is_max_weight_base, FinBase_exchange_mem_circuit_Finbase (hB) (hC) (heB) (hCe) (hb)]

private lemma greedy_lg_fil_ne
    {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β] [IsOrderedCancelAddMonoid β]
    {M : FinMatroid α} {c : α → β} {T : Finset α} (hT_base : IsFinBase M T)
    (hT_weight : weight c (greedy M.toIndepSystem c).toFinset < weight c T)
    (lg lg_fil : List α) (hlg : lg = M.E.toList.mergeSort (fun x y ↦ (weightRel' c) x y))
    (hlg_fil : lg_fil = lg.filter (fun x ↦ x ∈ (greedy M c).toFinset ∧ x ∉ T)) :
    lg_fil ≠ [] := by
  rw [hlg_fil]
  by_contra hc
  have hc := filter_eq_nil_iff.mp hc
  have hgsubT : (greedy M c).toFinset ⊆ T := by
    intro a ha
    by_contra hca
    have := hc a ?_
    · apply this
      refine (Bool.decide_iff _).mpr ⟨ha, hca⟩
    · rw [hlg, mem_mergeSort, mem_toList]
      refine mem_of_subset ?_ ha
      exact M.subset_ground (greedy_IsFinBase M c).left
  have hTsubg := (greedy_IsFinBase M c).right hT_base.left hgsubT
  rw [le_iff_subset] at hTsubg
  rwa [← Subset.antisymm hTsubg hgsubT, lt_self_iff_false] at hT_weight

theorem greedy_max_weight {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] (M : FinMatroid α) (c : α → β) :
    is_max_weight_base M c (greedy M c).toFinset := by
  refine ⟨greedy_IsFinBase M c, ?_⟩
  by_contra! hc
  obtain ⟨T, hT_base, hT_maxw, hT_weight, hT_mint⟩ := greedy_exists_T hc
  set lg := M.E.toList.mergeSort (fun x y ↦ (weightRel' c) x y) with hlg
  set lg_fil := lg.filter (fun x ↦ x ∈ (greedy M c).toFinset ∧ x ∉ T) with hlg_fil
  have hlg_len : lg_fil.length - 1 < lg_fil.length := by
    refine Nat.sub_one_lt ?_
    simp [greedy_lg_fil_ne (hT_base) (hT_weight) (lg) (lg_fil) (hlg) (hlg_fil)]
  set x := lg_fil[lg_fil.length - 1]'(hlg_len) with hx
  have hxlg_f : x ∈ lg_fil := by refine getElem_mem ?_
  simp only [hlg_fil, mem_toFinset, Bool.decide_and, decide_not, mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at hxlg_f
  obtain ⟨C, hCx, hC, hxT⟩ := FinBase_mem_insert_circuit hT_base (by
    rw [hlg, mem_mergeSort, mem_toList] at hxlg_f
    rw [mem_sdiff]
    refine ⟨hxlg_f.1, hxlg_f.2.2⟩)
  obtain ⟨y, hy⟩ := FinCircuit_ex_mem_nin_Indep (greedy_IsFinBase M c).1 (hC)
  have hy' : y ∈ C \ {x} := by by_contra; simp_all
  have hyT : y ∈ T := by
    have : C \ {x} ⊆ T := by
      rw [subset_insert_iff] at hCx
      rwa [sdiff_singleton_eq_erase]
    exact mem_def.mpr (this hy')
  set T' := insert x T \ {y} with hT'
  by_cases hcxy : c y = c x
--
  · have hT'_weq : weight c T = weight c T' := by
      have h₁ : x ≠ y := by by_contra!; simp_all
      have h₂ : Disjoint {y} (T \ {y}) := Disjoint.symm sdiff_disjoint
      have h₃ : Disjoint {x} (T \ {y}) := by simp_all
      calc weight c T = weight c ((T \ {y}) ∪ {y}) := by simp_all
              _ = weight c {y} + weight c (T \ {y}) := by grind [weight_of_union] --rw [weight_of_union, add_comm]; exact sdiff_disjoint
              _ = c y + weight c (T \ {y}) := by grind only [weight, sum_singleton']
              _ = c x + weight c (T \ {y}) := (add_left_inj (weight c (T \ {y}))).mpr hcxy
              _ = weight c {x} + weight c (T \ {y}) := by grind only [weight, sum_singleton']
              _ = weight c ({x} ∪ (T \ {y})) := by
                rw [weight_of_union]; exact disjoint_of_subset_left (fun ⦃a⦄ a_1 ↦ a_1) h₃
              _ = weight c (insert x T \ {y}) := ?_
      · rw [singleton_union x (T \ {y}), ← insert_sdiff_of_notMem T ?_]
        exact notMem_singleton.mpr h₁
--
    refine (not_lt_of_ge (hT_mint T' ?_)) ?_
    · exact ⟨FinBase_exchange_mem_circuit_Finbase hT_base hC hxT hCx hy', Eq.symm hT'_weq⟩
    · have : (T' ∩ (greedy M c).toFinset) = insert x (T ∩ (greedy M c).toFinset) := by
        rw [hT', sdiff_inter_right_comm, insert_inter_of_mem ?_]
        all_goals simp_all
      simp_all
--
  · have hxy : c x < c y := Std.lt_of_le_of_ne
      (FinBase_maxweight_no_change hT_base hT_maxw hxT hC hCx hy')
      (by intro a; exact hcxy (Eq.symm a))
    have hlgp : Pairwise (weightRel' c) lg := pairwise_mergeSort' (weightRel' c) M.E.toList
    have hsel_eq := Greedy.selectRel_eq_list_selectRel (M.indep_subset) (weightRel' c)
      (nodup_toList M.E) (by
      intro x y hx hy h
      exact (inferInstance : IsAntisymm α (weightRel' c)).antisymm (a := x) (b := y) h.1 h.2)
--
    obtain ⟨n, hn, hnx⟩ := getElem_of_mem hxlg_f.1
    obtain ⟨m, hm, hmy⟩ := getElem_of_mem (l := lg) (a := y) (by
      refine mem_mergeSort.mpr ?_
      rw [mem_sdiff] at hy
      exact mem_toList.mpr (Set.mem_of_subset_of_mem hC.1.2 hy.1))
    have hnm : lg.length - m - 1 ≤ lg.length - n - 1 := by
      have : n ≤ m := by
        by_contra! h
        have : (⟨m, hm⟩ : Fin lg.length) < ⟨n, hn⟩ := Fin.mk_lt_mk.mpr h
        have := Pairwise.rel_get_of_lt hlgp (b := ⟨n, hn⟩) (a := ⟨m, hm⟩) this
        simp only [get_eq_getElem, hmy, hnx] at this
        exact (not_le_of_gt hxy) (by simpa [Order.Preimage] using this.1)
      gcongr
    have hxyB := List.Greedy.select_monotone (P := M.Indep) (xs := lg) hnm
    set B_x := (List.Greedy.select M.Indep (lg.rtake (lg.length - n - 1))) with hB_x
    set B_y := (List.Greedy.select M.Indep (lg.rtake (lg.length - m - 1))) with hB_y
--
    have hBy_ind : M.Indep (insert y B_y.toFinset) := by
      have hxyB' : B_y.toFinset ⊆ B_x.toFinset := by
        intro a ha
        refine mem_toFinset.mpr ?_
        exact Sublist.mem (mem_dedup.mp ha) hxyB
      have hBx_T : B_x.toFinset ⊆ T := by
        intro a ha
        rw [hB_x] at ha
        by_contra haT
--
        have hafil : a ∈ lg_fil := by
          simp only [hlg_fil, mem_toFinset, Bool.decide_and, decide_not, List.mem_filter,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not]
          have h₁ : B_x.Sublist (greedy M c) := by
            rw [greedy, hsel_eq]
            exact List.Greedy.select_sublist' (lg.length - n - 1)
          have h₂ : (greedy M c).Sublist lg := by
            rw [greedy, hsel_eq]
            exact List.Greedy.select_sublist
          have h₃ : a ∈ lg := h₂.subset (h₁.subset (mem_toFinset.mp ha))
          refine ⟨h₃, ⟨h₁.subset (mem_toFinset.mp ha), haT⟩⟩
        obtain ⟨i, hi, hia⟩ := getElem_of_mem hafil
--
        have halgr : a ∈ (lg.rtake (lg.length - n - 1)) :=
          Sublist.mem (mem_toFinset.mp ha) (List.Greedy.select_sublist)
        rw [rtake, mem_drop_iff_getElem] at halgr
        obtain ⟨k, hk, hka⟩ := halgr
        rw [add_comm] at hk
        rw [pairwise_iff_getElem] at hlgp
        have h₀ : weightRel' c x a := by
          rw [← hka, ← hnx]
          refine hlgp _ _ hn hk ?_
          omega
        have h₁ : lg_fil.Pairwise (weightRel' c) := by
          refine Pairwise.filter _ ?_
          exact pairwise_mergeSort' (weightRel' c) M.E.toList
--
        rw [pairwise_iff_getElem] at h₁
        have h₂ : weightRel' c a x := by
          by_cases hxa : a = x
          · rw [hxa]
            exact or_self_iff.mp (total_of (weightRel' c) x x)
          · rw [hx, ← hia]
            refine h₁ _ _ hi ?_ ?_
            · refine Nat.lt_iff_le_and_ne.mpr ⟨Nat.le_sub_one_of_lt hi, ?_⟩
              rw [hx, ← hia] at hxa
              by_contra hc
              apply hxa
              rw [Nodup.getElem_inj_iff ?_]
              · exact hc
              · exact Nodup.filter _ (nodup_mergeSort.mpr (nodup_toList M.E))
        have := antisymm_of (weightRel' c) h₀ h₂
        rw [← hnx, ← hka, Nodup.getElem_inj_iff (nodup_mergeSort.mpr (nodup_toList M.E))] at this
        omega
      refine M.indep_subset hT_base.left ?_
      refine insert_subset_iff.mpr ⟨hyT, ?_⟩
      exact trans_of _ hxyB' hBx_T
    rw [mem_sdiff] at hy
    apply hy.right
    rw [← hmy] at hBy_ind ⊢
    rw [greedy_eq, List.Greedy.selectRel, ← hlg]
    have hylg_eq :=
      List.Greedy.select_iff (P := M.Indep) (hl := nodup_mergeSort.mpr (nodup_toList M.E)) hm
    exact mem_toFinset.mpr (hylg_eq.mpr hBy_ind)

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
    | inl h' => simp only [hx, Finset.mem_singleton] at h'; left; exact h'
    | inr h' => right; grind
  · intro h
    rw [mem_insert] at h
    cases h with
    | inl h' => rw [h']; exact hx'.left
    | inr h' => exact hXY h'

private def c {α : Type*} [DecidableEq α] (X Y : Finset α) := fun x ↦
  if x ∈ X then
    #(X \ Y) + #(Y \ X)
  else
    if x ∈ Y then
      2 * #(X \ Y)
    else
      0

private lemma c_zero_lt_neg_pos {α : Type*} [DecidableEq α] {X Y : Finset α} (h : X \ Y ≠ ∅) :
    0 < 2 * #(X \ Y) := by
  grind only [= card_sdiff, usr card_ne_zero_of_mem, ← notMem_empty]

private lemma c_neg_pos_lt_pos {α : Type*} [DecidableEq α] (X Y : Finset α) (h : #Y = #X + 1) :
    2 * #(X \ Y) < #(X \ Y) + #(Y \ X) := by
  grind only [usr card_sdiff_add_card_inter, usr card_union_add_card_inter]

private lemma c_weight_X {α : Type*} [DecidableEq α] (X Y : Finset α) :
    weight (c X Y) X = #X * (#(X \ Y) + #(Y \ X)) := by
  simp [weight, c, sum_ite_of_true]

private lemma c_weight_Y {α : Type*} [DecidableEq α] (X Y : Finset α) :
    weight (c X Y) Y = #(Y \ X) * (2 * #(X \ Y)) + #(X ∩ Y) * (#(X \ Y) + #(Y \ X)):= by
  nth_rw 2 [← sdiff_union_inter Y X]
  rw [weight_of_union (c X Y) (disjoint_sdiff_inter Y X)]
  simp only [weight, c]
  rw [sum_ite_of_false (by simp), sum_ite_of_true (by grind), sum_ite_of_true (by grind)]
  simp [inter_comm]

private lemma c_weight_X_lt_Y {α : Type*} [DecidableEq α] (X Y : Finset α) (h₁ : X \ Y ≠ ∅)
    (h₂ : #Y = #X + 1) : weight (c X Y) X < weight (c X Y) Y := by
  nth_rw 1 [c_weight_X, c_weight_Y, ← sdiff_union_inter X Y,
    card_union_of_disjoint (disjoint_sdiff_inter X Y), add_mul, add_lt_add_iff_right]
  rw [two_mul, mul_add, mul_add, mul_comm #(Y \ X) #(X \ Y), add_lt_add_iff_right]
  rw [mul_lt_mul_iff_right₀ (card_pos.mpr (nonempty_iff_ne_empty.mpr h₁))]
  grind only [usr card_sdiff_add_card_inter, usr card_union_add_card_inter]

private lemma c_greedy_partition {α : Type*} [Encodable α] {F : IndepSystem α} {X Y : Finset α}
    (hX : F.Indep X) (hY : F.Indep Y) (h₁ : X \ Y ≠ ∅) (h₂ : #Y = #X + 1) :
    F.E.toList.mergeSort (fun x y ↦ decide (weightRel' (c X Y) x y)) =
    (F.E \ (X ∪ Y)).sort (weightRel' (c X Y)) ++ (Y \ X).sort (weightRel' (c X Y))
    ++ X.sort (weightRel' (c X Y)) := by
  set lX := X.sort (weightRel' (c X Y)) with hlX
  set lY := (Y \ X).sort (weightRel' (c X Y)) with hlY
  set lC := (F.E \ (X ∪ Y)).sort (weightRel' (c X Y)) with hlC
  have hlX₁ : ∀ {a}, a ∈ lX → (c X Y) a = #(X \ Y) + #(Y \ X) := by
    intro a ha
    simp [c, (mem_sort _).mp ha]
  have hlY₁ : ∀ {a}, a ∈ lY → (c X Y) a = 2 * #(X \ Y) := by
    intro a ha
    simp [c, mem_sdiff.mp ((mem_sort _).mp ha)]
  have hlC₁ : ∀ {a}, a ∈ lC → (c X Y) a = 0 := by intro a ha; grind [c, (mem_sort _).mp ha]
  have hls : (lC ++ lY ++ lX).Pairwise (weightRel' (c X Y)) := by
    rw [pairwise_append, pairwise_append]
    refine ⟨?_, pairwise_sort _ _, ?_⟩
    · refine ⟨pairwise_sort _ _, pairwise_sort _ _, ?_⟩
      intro a ha b hb
      exact weightRel'_of_weight_lt (c X Y) (by grind [hlC₁ ha, hlY₁ hb])
    · intro a ha b hb
      cases mem_append.mp ha with
      | inl hac =>
        exact weightRel'_of_weight_lt (c X Y) <|
          by rw [hlC₁ hac, hlX₁ hb]; exact Nat.zero_lt_of_lt (c_neg_pos_lt_pos _ _ h₂)
      | inr hac =>
        exact weightRel'_of_weight_lt (c X Y) <|
          by rw [hlY₁ hac, hlX₁ hb]; exact (c_neg_pos_lt_pos _ _ h₂)
  refine Perm.eq_of_pairwise' (pairwise_mergeSort' _ _) hls ?_
  refine (perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact nodup_mergeSort.mpr (nodup_toList F.E)
  · rw [nodup_append', nodup_append']
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
  · intro a
    rw [mem_append, mem_append, mem_sort _, mem_sort _, mem_sort _, mem_mergeSort, mem_toList]
    rw [← mem_union, ← mem_union, union_assoc, sdiff_union_self_eq_union, union_comm X Y]
    rw [sdiff_union_of_subset ?_]
    exact union_subset_iff.mpr ⟨F.subset_ground hY, F.subset_ground hX⟩

private lemma c_greedy_sublist_X {α : Type*} [Encodable α] {F : IndepSystem α} (X Y : Finset α)
    (hX : F.Indep X) :
    ∀ l, l <+ X.sort (weightRel' (c X Y)) → List.Greedy.select F.Indep l = l := by
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

private lemma c_greedy_sublist_Y {α : Type*} [Encodable α] {F : IndepSystem α} (X Y : Finset α)
    (hX : F.Indep X) (hc : ∀ x ∈ Y, x ∉ X → ¬F.Indep (insert x X)) :
    ∀ l, l <+ (Y \ X).sort (weightRel' (c X Y)) →
    List.Greedy.select F.Indep (l ++ X.sort (weightRel' (c X Y))) = X.sort (weightRel' (c X Y))
    := by
  have hlY₁ : ∀ {a}, a ∈ (Y \ X).sort (weightRel' (c X Y)) → (c X Y) a = 2 * #(X \ Y) := by
    intro a ha
    simp [c, mem_sdiff.mp ((mem_sort _).mp ha)]
  intro l hl
  induction l with
  | nil => simp [c_greedy_sublist_X X Y hX]
  | cons x xs ih =>
    rw [cons_append, Greedy.select_cons_neg ?_, ih (sublist_of_cons_sublist hl)]
    rw [ih (sublist_of_cons_sublist hl), sort_toFinset]
    refine hc x ?_ ?_
    <;> simp [(mem_sdiff.mp ((mem_sort _).mp (mem_of_cons_sublist hl)))]

private lemma c_weight_greedy_eq_X {α : Type*} [Encodable α] (F : IndepSystem α) (X Y : Finset α)
    (hX : F.Indep X) (hY : F.Indep Y) (h₁ : X \ Y ≠ ∅) (h₂ : #Y = #X + 1)
    (hc : ∀ x ∈ Y, x ∉ X → ¬F.Indep (insert x X)) :
    weight (c X Y) (greedy F (c X Y)).toFinset = weight (c X Y) X := by
    set lB := (List.Greedy.select F.Indep (F.E.toList.mergeSort
      (fun x y ↦ decide (weightRel' (c X Y) x y)))) with hlB
    set lX := X.sort (weightRel' (c X Y)) with hlX
    set lY := (Y \ X).sort (weightRel' (c X Y)) with hlY
    set lC := (F.E \ (X ∪ Y)).sort (weightRel' (c X Y)) with hlC
    have hlB₁ : lX ⊆ lB := by
      refine Sublist.subset ?_
      rw [← c_greedy_sublist_X X Y hX lX (by simp [hlX]), hlB, c_greedy_partition hX hY h₁ h₂]
      exact List.Greedy.select_monotone' _ lX
    have hlB₂ : lB ⊆ lX ∪ lC := by
      trans
      · refine Sublist.subset (l₂ := lC ++ lX) ?_
        rw [hlX, ← c_greedy_sublist_Y X Y hX hc lY (by simp [hlY]), hlB,
          c_greedy_partition hX hY h₁ h₂, append_assoc]
        refine List.Greedy.select_append_sublist (P := F.Indep)
      · grind only [= List.subset_def, = mem_union_iff, = mem_append]
    rw [greedy_eq, List.Greedy.selectRel]
    rw [c_weight_X, weight, ← sdiff_union_inter lB.toFinset X]
    simp only [c]
    rw [sum_union (disjoint_sdiff_inter _ _), sum_ite_of_false (by simp), sum_ite_of_false ?_,
      sum_const_zero]
    · rw [inter_eq_right.mpr ?_, sum_ite_of_true (by simp), sum_const, zero_add]
      · simp
      · intro x hx
        exact mem_toFinset.mpr (hlB₁ ((mem_sort (weightRel' (c X Y))).mpr hx))
    · intro x hx
      obtain ⟨hx₁, hx₂⟩ := mem_sdiff.mp hx
      cases mem_union_iff.mp (hlB₂ (mem_toFinset.mp hx₁)) with
      | inl hx₃ => exact False.elim (hx₂ ((mem_sort _).mp hx₃))
      | inr hx₃ => rw [mem_sort _] at hx₃; grind

theorem Matroid_of_greedy {α : Type*} [Encodable α] (F : IndepSystem α)
    (h : ∀ {β : Type}, [LinearOrder β] → [AddCommMonoid β] → [IsOrderedCancelAddMonoid β] →
      ∀ c : α → β, is_max_weight_base F c (greedy F c).toFinset) : IsFinMatroid F := by
  apply IndepSystem.augmentation_of_succ _ F.indep_subset
  intro Y X hY hX h_card
  by_cases hXY₁ : X \ Y = ∅
  · obtain ⟨x, hx⟩ := exists_eq_insert_of_card_succ (sdiff_eq_empty_iff_subset.mp hXY₁) h_card
    refine ⟨x, hx.left, hx.right.left, by rwa [← hx.right.right]⟩
  · by_contra! hc
    obtain ⟨B', hB'₁, hB'₂⟩ := exists_IsFinBase_superset hY
    have hwB' : weight (c X Y) Y ≤ weight (c X Y) B' := by
      rw [← sdiff_union_inter B' Y, inter_comm, inter_eq_left.mpr hB'₂, union_comm]
      refine weight_monotone_of_pos (c := (c X Y)) ?_
      grind
    exact (lt_self_iff_false _).mp (calc weight (c X Y) (greedy F (c X Y)).toFinset
    _ = weight (c X Y) X := c_weight_greedy_eq_X F X Y hX hY hXY₁ h_card hc
    _ < weight (c X Y) Y := c_weight_X_lt_Y X Y hXY₁ h_card
    _ ≤ weight (c X Y) B' := hwB'
    _ ≤ weight (c X Y) (greedy F (c X Y)).toFinset := (h (c X Y)).right B' hB'₁)

theorem Matroid_iff_greedy {α : Type*} [Encodable α] (F : IndepSystem α) :
    IsFinMatroid F ↔ (∀ {β : Type}, [LinearOrder β] → [AddCommMonoid β] →
    [IsOrderedCancelAddMonoid β] → ∀ c : α → β, is_max_weight_base F c (greedy F c).toFinset) := by
  refine ⟨?_, ?_⟩
  · intro h β _ _ _ c
    exact greedy_max_weight (FinMatroid_of_IsFinMatroid h) c
  · intro h
    exact Matroid_of_greedy F h

end FinMatroid
