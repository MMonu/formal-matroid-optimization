import Mathlib.Tactic

import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.FinMatroid.FinBases
import FormalMatroidOptimization.FinMatroid.FinCircuit
import FormalMatroidOptimization.Greedy.Basic
import FormalMatroidOptimization.List.Greedy
import Mathlib.Order.Minimal
import Mathlib.Deprecated.Sort
import Mathlib.Data.List.GetD

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
    [IsOrderedCancelAddMonoid β] {c : α → β} (h : ∀ a, 0 ≤ c a) {X : Finset α} :
    0 ≤ weight c X := by
  refine Finset.induction_on X ?_ ?_
  · simp [weight]
  · intro y Y hyY ih
    rw [weight, Finset.sum_insert hyY]
    have := add_le_add (h y) ih
    rwa [zero_add, weight] at this

lemma weight_monotone_of_pos {α β : Type*} [DecidableEq α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] {c : α → β} (h : ∀ a, 0 ≤ c a) {X Y : Finset α} :
    weight c X ≤ weight c (X ∪ Y) := by
  nth_rw 1 [← Finset.union_sdiff_self_eq_union, weight_of_union, ← add_zero (weight c X)]
  · exact add_le_add (by simp) (weight_pos_of_pos h)
  · exact Finset.disjoint_sdiff

def is_min_weight_base {α β : Type*} [DecidableEq α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] (F : IndepSystem α) (c : α → β) (B : Finset α) : Prop :=
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

lemma weightRel'_eq {α β : Type*} [Encodable α] [LinearOrder β] {c : α → β} :
  weightRel' c = fun

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

instance {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] (c : α → β) :
    DecidableRel (weightRel c) := Classical.decRel (weightRel c)
end

local instance {α : Type*} [Encodable α] : DecidableEq α := Encodable.decidableEqOfEncodable α

def IsFinBase_eq {α : Type*} [DecidableEq α] (F : IndepSystem α) (I : Finset α) :
    IsFinBase F I ↔ (F.Indep I ∧ F.E.powerset.filter (fun J ↦ F.Indep J ∧ I ⊂ J) = ∅) := by
  rw [IsFinBase, Maximal, Finset.filter_eq_empty_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨h, h₁⟩
    refine ⟨h, ?_⟩
    intro h₂ J ⟨h₃, h₄⟩
    grind [Finset.le_iff_subset.mp (h₁ h₃ (le_of_lt (Finset.lt_iff_ssubset.mpr h₄)))]
  · intro ⟨h, h₁⟩
    refine ⟨h, ?_⟩
    intro J h₂ h₃
    have := (not_and.mp (h₁ (Finset.mem_powerset.mpr (F.subset_ground h₂)))) h₂
    rw [Finset.le_iff_subset] at h₃ ⊢
    grind

instance {α β : Type*}  [DecidableEq α] [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] {c : α → β}
    {F : IndepSystem α} : DecidablePred (is_min_weight_base F c) := by
  sorry

instance {α : Type*} [DecidableEq α] {F : IndepSystem α} : DecidablePred (IsFinBase F) := by sorry

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

lemma FinBases_notsub {α : Type*} [DecidableEq α] {M : FinMatroid α} {X X' : Finset α}
    (hX : IsFinBase M X) (hX' : IsFinBase M X') (hneq : X ≠ X') : ∃ x, x ∈ X \ X' := by
  have hnX : ¬ X ⊆ X' := by
    by_contra
    have h := hX.2 hX'.1 this
    grind only [Finset.le_iff_subset, Finset.subset_iff]
  rw [Finset.not_subset] at hnX
  simp_all only [ne_eq, Finset.mem_sdiff]

lemma FinDep_exists_FinCircuit_subset {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {X : Finset α} (hX : FinDep M X) : ∃ C ⊆ X, IsFinCircuit M C :=
  exists_minimal_le_of_wellFoundedLT (FinDep M) X hX

lemma FinCircuit_ex_mem_nin_FinBase {α : Type*} [DecidableEq α] {M : FinMatroid α} {B C : Finset α}
    (hB : IsFinBase M B) (hC : IsFinCircuit M C) : ∃ e, e ∈ C \ B := by
  by_contra
  have : C ⊆ B := by simp_all; grind
  grind [M.indep_subset hB.1, hC.1, FinDep]

lemma FinBase_mem_insert_circuit_mem {α : Type*} [DecidableEq α] {M : FinMatroid α} {e : α}
    {B C : Finset α} (hB : IsFinBase M B) (hC : IsFinCircuit M C) (hCB : C ⊆ (insert e B)) :
    e ∈ C \ B := by
  grind [M.indep_subset hB.1, hC.1, FinDep]

lemma FinBase_mem_insert_circuit {α : Type*} [DecidableEq α] {M : FinMatroid α} {e : α}
    {B : Finset α} (hB : IsFinBase M B) (he : e ∈ M.E \ B) :
    ∃ C ⊆ (insert e B), IsFinCircuit M C ∧ e ∈ C \ B := by
  have he' : e ∈ M.toMatroid.E \ B := by
    rw [Set.mem_diff]
    rw [Finset.mem_sdiff] at he
    exact (Set.mem_diff e).mp he
  have hBe_dep : FinDep M (insert e B) := by
    have := Matroid.IsBase.insert_dep (M := M.toMatroid) ((IsFinBase_iff_IsBase M B).mp hB) he'
    grind [Matroid.IsBase.insert_dep, (FinDep_iff_Dep M (insert e B)).mpr, Finset.coe_insert]
  grind [FinDep_exists_FinCircuit_subset hBe_dep, FinBase_mem_insert_circuit_mem]

lemma FinCircuit_ex_mem_nin_Indep {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {I C : Finset α} (hI : M.Indep I) (hC : IsFinCircuit M C) : ∃ c, c ∈ C \ I := by
  by_contra!
  simp only [Finset.mem_sdiff, not_and, Decidable.not_not, ← Finset.subset_iff] at this
  grind [M.indep_subset hI this, hC.1, FinDep]

lemma FinIndep_exchange_mem_circuit_FinIndep {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {e f : α} {I C : Finset α} (hI : M.Indep I) (hC : IsFinCircuit M C) (heI : e ∈ C \ I)
    (hCe : C ⊆ (insert e I)) (hf : f ∈ C \ {e}) : M.Indep (insert e I \ {f}) := by
  refine (FinIndep_iff_Indep M (insert e I \ {f})).mpr ?_
  have he_cl : e ∈ M.toMatroid.closure ↑I := by
    have hdep : FinDep M (insert e I) := by
      constructor
      · by_contra
        grind [M.indep_subset this hCe, hC.1, FinDep]
      · rw [Finset.insert_eq e I]
        refine Finset.union_subset ?_ (M.subset_ground (X := I) hI)
        grind only [Finset.mem_sdiff, hC.1.2, Finset.subset_iff, Finset.singleton_subset_iff]
    have := (Matroid.Indep.mem_closure_iff (x := e) ((FinIndep_iff_Indep M I).mp hI)).mpr
    simp_all only [Finset.mem_sdiff, Finset.mem_singleton, SetLike.mem_coe, or_false]
    rw [← Finset.coe_insert e I] at this
    exact this ((FinDep_iff_Dep M (insert e I)).mp hdep)
  have he_func : f ∈ M.toMatroid.fundCircuit e ↑I := by
    have : C ⊆ (insert e I) → SetLike.coe C ⊆ insert e (SetLike.coe I) := by grind
    have := Matroid.IsCircuit.eq_fundCircuit_of_subset ((FinCircuit_iff_Circuit M C).mp hC)
      ((FinIndep_iff_Indep M I).mp hI) (this hCe)
    grind only [Finset.mem_sdiff, Finset.mem_coe]
  rw [Finset.mem_sdiff] at heI
  have := ((Matroid.Indep.mem_fundCircuit_iff
    ((FinIndep_iff_Indep M I).mp hI)) he_cl heI.2).mp he_func
  grind [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]

lemma FinBase_exchange_mem_circuit_Finbase {α : Type*} [DecidableEq α] {M : FinMatroid α}
    {b e : α} {B C : Finset α} (hB : IsFinBase M B) (hC : IsFinCircuit M C) (heB : e ∈ C \ B)
    (hCe : C ⊆ (insert e B)) (hb : b ∈ C \ {e}) : IsFinBase M (insert e B \ {b}) := by
  have hb' : b ∈ B := by grind
  have he' : e ∉ B := by grind
  have hI := FinIndep_exchange_mem_circuit_FinIndep (f := b) (I := B) (hB.1) (hC) (heB) (hCe) (hb)
  have hI' : M.toMatroid.Indep (insert e ↑B \ {b}) := by
    have := ((FinIndep_iff_Indep M (insert e B \ {b})).mp hI)
    simp_all
  have := Matroid.IsBase.exchange_isBase_of_indep' (M := M.toMatroid)
    ((IsFinBase_iff_IsBase M B).mp hB) (hb') (he') hI'
  have : M.toMatroid.IsBase ↑(insert e B \ {b}) := by simp_all
  exact (IsFinBase_iff_IsBase M (insert e B \ {b})).mpr this

lemma greedy_exists_T {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] {M : FinMatroid α} {c : α → β} {A : Finset α}
    (hex : ∃ X, IsFinBase M X ∧ weight c A < weight c X) :
    ∃ B, IsFinBase M B ∧
        (is_min_weight_base M c B) ∧
        (weight c A < weight c B) ∧
        (∀ X, IsFinBase M X ∧ weight c X = weight c B → (X ∩ A).card ≤ (B ∩ A).card) := by
  set sT' := M.E.powerset.filter (fun X ↦ IsFinBase M X ∧ weight c A < weight c X) with hsT'
  have : sT'.Nonempty := by
    obtain ⟨X, hXb, hXw⟩ := hex
    use X
    grind [M.subset_ground hXb.1]
  have := Finset.exists_max_image sT' (fun X ↦ weight c X) this
  obtain ⟨C, hC, hC_maxw⟩ := this
  set sT := sT'.filter (fun X ↦ weight c X = weight c C) with hsT
  have : sT.Nonempty := by
    use C
    grind only [Finset.mem_filter]
  have := Finset.exists_max_image sT (fun X : Finset α ↦ (X ∩ A).card) this
  obtain ⟨T, hT, hT_int⟩ := this
  rw [hsT, Finset.mem_filter] at hT
  obtain ⟨hT', hT_maxw'⟩ := hT
  simp only [hsT', Finset.mem_filter, Finset.mem_powerset] at hT'
  obtain ⟨hT_sub, hT_base, hT_weight⟩ := hT'
  have hT_maxw : is_min_weight_base M c T := by
    refine ⟨hT_base, ?_⟩
    intro B hB
    by_cases hBsT' : B ∈ sT'
    · simp_all [hC_maxw B hBsT']
    · simp only [hsT', Finset.mem_filter, Finset.mem_powerset, not_and, not_lt] at hBsT'
      grind [hBsT' (M.subset_ground hB.1) hB]
  use T
  refine ⟨hT_base, ⟨hT_maxw, ⟨hT_weight, ?_⟩⟩⟩
  intro X ⟨hX1, hX2⟩
  have : X ∈ sT := by
    simp only [hsT, Finset.mem_filter]
    rw [hT_maxw'] at hX2
    refine ⟨?_, hX2⟩
    simp only [hsT', Finset.mem_filter, Finset.mem_powerset]
    rw [hT_maxw', ← hX2] at hT_weight
    refine ⟨M.subset_ground hX1.1, ⟨hX1, hT_weight⟩⟩
  grind

lemma FinBase_maxweight_no_change {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] {M : FinMatroid α} {c : α → β} {B C : Finset α} {b e : α}
    (hB : IsFinBase M B) (hm : is_min_weight_base M c B) (heB : e ∈ C \ B) (hC : IsFinCircuit M C)
    (hCe : C ⊆ (insert e B)) (hb : b ∈ C \ {e}) : c e ≤ c b := by
  by_contra!
  have hB' := FinBase_exchange_mem_circuit_Finbase (hB) (hC) (heB) (hCe) (hb)
  have : weight c B < weight c (insert e B \ {b}) := by
    have h1 : {b} ⊆ B := by grind
    have h2 : Disjoint {b} (B \ {b}) := Disjoint.symm Finset.sdiff_disjoint
    have h3 : Disjoint {e} (B \ {b}) := by simp_all
    have h4 : e ≠ b := by grind
    calc weight c B = weight c ((B \ {b}) ∪ {b}) := by simp_all
                  _ = weight c {b} + weight c (B \ {b}) := by grind [weight_of_union]
                  _ = c b + weight c (B \ {b}) := by grind [weight]
                  _ < c e + weight c (B \ {b}) := by simp_all [add_lt_add_iff_right]
                  _ = weight c {e} + weight c (B \ {b}) := by grind [weight]
                  _ = weight c ({e} ∪ (B \ {b})) := by grind [weight_of_union]
                  _ = weight c (insert e B \ {b}) := ?_
    · rw [Finset.singleton_union e (B \ {b})]
      have hm : insert e (B \ {b}) = insert e B \ {b} := by
        rw [← Finset.insert_sdiff_of_notMem B ?_]
        simp_all
      simp_all
  grind [is_min_weight_base]

open Finset in
theorem greedy_min_weight {α β : Type*} [Encodable α] [LinearOrder β] [AddCommMonoid β]
    [IsOrderedCancelAddMonoid β] (M : FinMatroid α) (c : α → β) :
    is_min_weight_base M c (greedy M c).toFinset := by
  refine ⟨greedy_IsFinBase M c, ?_⟩
  by_contra! hc
  obtain ⟨T, hT_base, hT_maxw, hT_weight, hT_mint⟩ := greedy_exists_T hc
  set lg := M.E.toList.mergeSort (fun x y ↦ (weightRel' c) x y) with hlg
  set lg_fil := lg.reverse.filter (fun x ↦ x ∈ (greedy M c).toFinset ∧ x ∉ T) with hlg_fil

  set x := lg_fil[0]'(?_) with hx
  · have hxlg_f : x ∈ lg_fil := by refine List.getElem_mem ?_
    simp [hlg_fil] at hxlg_f
    --have hx1 : x ∈ (greedy M c).toFinset \ T := by rw [mem_sdiff] simp_all
    have hxin : x ∈ M.E \ T := by
      rw [mem_sdiff]
      simp [hlg] at hxlg_f
      refine ⟨hxlg_f.1, hxlg_f.2.2⟩
    have hC := FinBase_mem_insert_circuit hT_base hxin
    obtain ⟨C, hCx, hC, hxT⟩ := hC
    have hCB := FinCircuit_ex_mem_nin_Indep (greedy_IsFinBase M c).1 (hC)
    obtain ⟨y, hy⟩ := hCB
    have hy' : y ∈ C \ {x} := by by_contra; simp_all
    have hyT : y ∈ T := by
      have : C \ {x} ⊆ T := by
        rw [subset_insert_iff] at hCx
        rw [sdiff_singleton_eq_erase x C]
        exact coe_subset.mp hCx
      exact mem_def.mpr (this hy')
    have hT'_base := FinBase_exchange_mem_circuit_Finbase hT_base hC hxT hCx (hy')
    have hy_weight := FinBase_maxweight_no_change (hT_base) (hT_maxw) (hxT) (hC) (hCx) (hy')
    set T' := insert x T \ {y} with hT'
    by_cases hcxy : c y = c x
    · have hT'_weq : weight c T = weight c T' := by
        have h0 : x ≠ y := by by_contra!; simp_all
        have h2 : Disjoint {y} (T \ {y}) := Disjoint.symm Finset.sdiff_disjoint
        have h3 : Disjoint {x} (T \ {y}) := by simp_all
        calc weight c T = weight c ((T \ {y}) ∪ {y}) := by simp_all
                _ = weight c {y} + weight c (T \ {y}) := by rw [weight_of_union, add_comm]; exact sdiff_disjoint
                _ = c y + weight c (T \ {y}) := by simp_all [weight]
                _ = c x + weight c (T \ {y}) := by simp_all
                _ = weight c {x} + weight c (T \ {y}) := by simp_all [weight]
                _ = weight c ({x} ∪ (T \ {y})) := by rw [weight_of_union]; exact disjoint_of_subset_left (fun ⦃a⦄ a_1 ↦ a_1) h3
                _ = weight c (insert x T \ {y}) := ?_
        · rw [Finset.singleton_union x (T \ {y})]
          have hm : insert x (T \ {y}) = insert x T \ {y} := by
            rw [← insert_sdiff_of_notMem T ?_]
            simp_all
          simp_all

      have hT'_weight : weight c (greedy M.toIndepSystem c).toFinset < weight c T' := by
        exact lt_of_lt_of_eq hT_weight hT'_weq
      have hT'_int : #(T ∩ (greedy M c).toFinset) < #(T' ∩ (greedy M c).toFinset) := by
        have : (T' ∩ (greedy M c).toFinset) = insert x (T ∩ (greedy M c).toFinset) := by
          rw [hT', sdiff_inter_right_comm, insert_inter_of_mem ?_]
          all_goals simp_all
        simp_all
      have := hT_mint T' ⟨hT'_base, Eq.symm hT'_weq⟩
      exact (not_lt_of_ge this) hT'_int

    · have hxy : c x < c y := Std.lt_of_le_of_ne hy_weight fun a ↦ hcxy (id (Eq.symm a))

      have hxs : (M.E.toList).Nodup := nodup_toList M.E
      have hlgn : lg.Nodup := List.nodup_mergeSort.mpr hxs
      have hlgrn : lg.reverse.Nodup := by exact List.nodup_reverse.mpr hlgn
      have hlgp : List.Pairwise (weightRel' c) lg := List.pairwise_mergeSort' (weightRel' c) M.E.toList
      have hlgrp : List.Pairwise (fun a b => (weightRel' c) b a) lg.reverse := List.pairwise_reverse.mpr hlgp
      have hlgrlg := List.length_reverse (as := lg)

      have ha : ∀ (x y : α), x ∈ M.E.toList → y ∈ M.E.toList → weightRel' c x y ∧ weightRel' c y x → x = y := by
        intro x y hx hy h
        exact (inferInstance : IsAntisymm α (weightRel' c)).antisymm (a := x) (b := y) h.1 h.2
      have hsel_eq := Greedy.selectRel_eq_list_selectRel (M.indep_subset) (weightRel' c) (hxs) (ha)
      simp [List.Greedy.selectRel, ← hlg] at hsel_eq

      have hx_in : x ∈ lg := hxlg_f.1
      have hy_in : y ∈ lg := by
        refine List.mem_mergeSort.mpr ?_
        rw [mem_sdiff] at hy
        · exact mem_toList.mpr (Set.mem_of_subset_of_mem hC.1.2 hy.1)
      obtain ⟨n, hn, hnx⟩ := List.getElem_of_mem hx_in
      obtain ⟨m, hm, hmy⟩ := List.getElem_of_mem hy_in
      have hnm : n ≤ m := by
        by_contra! h
        have : (⟨m, hm⟩ : Fin lg.length) < ⟨n, hn⟩ := Fin.mk_lt_mk.mpr h
        have := List.Pairwise.rel_get_of_lt hlgp (b := ⟨n, hn⟩) (a := ⟨m, hm⟩) this
        simp [hnx, hmy] at this
        have := by simpa [Order.Preimage] using this.1
        exact (not_le_of_gt hxy) this
      have hnm' : lg.length - m - 1 ≤ lg.length - n - 1 := by gcongr
      have hx_ing : x ∈ greedy M c := by simp_all
      have hy_ning : y ∉ greedy M c := by simp_all
      have hx_ing' : lg[n] ∈ List.Greedy.select M.Indep lg := by
        simp [greedy, hsel_eq, ← hnx] at hx_ing
        exact hx_ing
      have hy_ning' : lg[m] ∉ List.Greedy.select M.Indep lg := by
        simp [greedy, hsel_eq, ← hmy] at hy_ning
        exact hy_ning
      obtain ⟨ng, hng, hngx⟩ := List.getElem_of_mem hx_ing
      have hxlg_eq := List.Greedy.select_iff (P := M.Indep) (xs := lg) (hl := List.nodup_mergeSort.mpr hxs) (n := n) hn
      have hylg_eq := List.Greedy.select_iff (P := M.Indep) (xs := lg) (hl := List.nodup_mergeSort.mpr hxs) (n := m) hm
      have hxB := hxlg_eq.mp hx_ing'
      have hxyB := List.Greedy.select_monotone (P := M.Indep) (xs := lg) hnm'
      set B_x := (List.Greedy.select M.Indep (lg.rtake (lg.length - n - 1))) with hB_x
      set B_y := (List.Greedy.select M.Indep (lg.rtake (lg.length - m - 1))) with hB_y

      have hBy_ind : M.Indep (insert y B_y.toFinset) := by
        have hxyB' : B_y.toFinset ⊆ B_x.toFinset := by
          intro a ha
          refine List.mem_toFinset.mpr ?_
          exact List.Sublist.mem (List.mem_dedup.mp ha) hxyB
        have hBx_T : B_x.toFinset ⊆ T := by
          intro a ha
          rw [hB_x] at ha
          by_contra haT

          have haB : a ∈ B_x := List.mem_toFinset.mp ha
          have hlg_filn := List.Nodup.filter (fun x ↦ decide (x ∈ (greedy M.toIndepSystem c).toFinset ∧ x ∉ T)) hlgrn
          have hafil : a ∈ lg_fil := by
            simp [hlg_fil]
            have h1 : B_x.Sublist (greedy M c) := by
              simp [greedy, hsel_eq]
              exact List.Greedy.select_sublist' (lg.length - n - 1)
            have h2 : (greedy M c).Sublist lg := by
              simp [greedy, hsel_eq]
              exact List.Greedy.select_sublist
            have h3 : a ∈ lg := h2.subset (h1.subset haB)
            refine ⟨h3, ⟨h1.subset haB, haT⟩⟩
          obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hafil
          have hia' := List.Nodup.idxOf_getElem hlg_filn i hi
          rw [hia, ← hlg_fil] at hia'

          have halgr : a ∈ (lg.rtake (lg.length - n - 1)) := by
            exact List.Sublist.mem haB (List.Greedy.select_sublist)
          simp [List.rtake] at halgr
          rw [List.mem_drop_iff_getElem] at halgr
          obtain ⟨k, hk, hka⟩ := halgr
          rw [add_comm] at hk
          have hxa : n < k + n + 1 := by omega

          rw [List.pairwise_iff_getElem] at hlgp

          have : weightRel' c x a := by
            rw [← hka, ← hnx]
            refine hlgp _ _ hn hk ?_
            omega
          sorry

/-
            --refine (List.pairwise_iff (weightRel' c) (lg)).mp (hlgp)
          have har : a = lg.reverse[lg.length - (k + n)] := by
            rw [← hka]
            nth_rw 1 [List.getElem_eq_getElem_reverse (List.mem_drop_iff_getElem._proof_2 k hk)]
            --nth_rw 1 [List.getElem_eq_getElem_reverse (List.mem_drop_iff_getElem._proof_2 k hk)]
            congr

            exact List.get_reverse' lg ⟨lg.length - 1 - (k + n + 1), ⟩
          have hlg_inj := (List.nodup_iff_injective_getElem (l := lg)).mp hlgn
          --have hka' : List.idxOf a lg = k + n + 1 := by sorry
          have : k + (lg.length - (lg.length - n - 1)) = k + n + 1 := by omega
          have hka' := List.Nodup.idxOf_getElem hlgn (k + (lg.length - (lg.length - n - 1))) hk
          have : lg.length - (lg.length - n - 1) + k = k + (lg.length - (lg.length - n - 1)) := by rw [Nat.add_comm]
          rw [Nat.add_comm] at hk
          --grw [Nat.add_comm] at hka

          have halgr : a ∈ lg.reverse := List.mem_of_mem_filter hafil
          have hkalgr : List.idxOf a lg = k + n + 1 := by sorry

          --rw [hka] at hka'
#check List.getElem_rotate

          have hk : k + n + 1 < lg.length := by omega
          --have : (⟨lg.length - (lg.length - n - 1) + k, ?_⟩ : Fin lg.length) = ⟨n + k + 1, ?_⟩ := by refine Fin.mk.congr_simp (lg.length - (lg.length - n - 1) + k) (n + k + 1) ?_ ?_ omega
          have hnk : n < k + n + 1 := by omega
          have hkhk : lg.length - 1 - (k + n + 1) < lg.length := by omega
          have hnhn : lg.length - 1 - n < lg.length := by omega
          have hkhk' : lg.length - 1 - (lg.reverse.length - (k + n + 1)) < lg.length := by omega
          set j := k + n + 1 with hj

          rw [← List.length_reverse (as := lg)] at hk hn
          have har : lg.reverse.get ⟨j, hk⟩ = lg[k] := by sorry --apply?
          have har' : lg.reverse.get ⟨j, hk⟩ = lg.get ⟨lg.length - 1 - j, hkhk⟩ := List.get_reverse' lg ⟨j, hk⟩ (hkhk)
          have hxr' : lg.reverse.get ⟨n, hn⟩ = lg.get ⟨lg.length - 1 - n, hnhn⟩ := List.get_reverse' lg ⟨n, hn⟩ (hnhn)

          have : i < 0 := by
            -- rw??
            have := List.Pairwise.filter (l := lg.reverse) (R := (fun x y ↦ (weightRel' c) x y)) (fun x ↦ x ∈ (greedy M c).toFinset ∧ x ∉ T)
            have : (fun x y ↦ (weightRel' c) x y) x a := by sorry

            --rw [← hlg_fil] at this
            sorry
          contradiction
-/

        have : (insert y B_x.toFinset) ⊆ T := by
          rw [insert_subset_iff]
          refine ⟨hyT, hBx_T⟩
        have hBxy_ind : M.Indep (insert y B_x.toFinset) := M.indep_subset hT_base.1 this
        have : insert y B_y.toFinset ⊆ insert y B_x.toFinset := insert_subset_insert y hxyB'
        exact M.indep_subset hBxy_ind this
      rw [← hmy] at hBy_ind
      have := hylg_eq.mpr hBy_ind
      contradiction
  ·
    have : (greedy M c).toFinset ≠ T := by
      by_contra
      have : weight c (greedy M.toIndepSystem c).toFinset = weight c T := by
        simp_all
      simp_all
    exact FinBases_notsub (X := (greedy M c).toFinset) (X' := T) (greedy_IsFinBase M c) (hT_base) this

/-
        have : lg = lg.mergeSort fun x y ↦ decide (weightRel' c x y) := by
          exact Eq.symm (List.mergeSort_eq_self (weightRel' c) hlgp)
        rw [List.Greedy.selectRel, ← this] at hsel_eq

      --have lgg : lg = lg.mergeSort fun x y ↦ decide (weightRel' c x y) := by
        --exact Eq.symm (List.mergeSort_eq_self (weightRel' c) hlgp)
      --have : List.Greedy.select M.Indep lg = List.Greedy.selectRel M.Indep (weightRel' c) lg := by

  set sT := M.E.powerset.filter
    (fun I ↦ is_min_weight_base M c I ∧ weight c (greedy M c).toFinset < weight c I) with hsT
  set f := fun J ↦ #((greedy M c).toFinset ∩ J)
  have : sT.Nonempty := by
    obtain ⟨T₁, hT₁b, hT₁w⟩ := hc
    set sT' := M.E.powerset.filter
      (fun I ↦ IsFinBase M I ∧ weight c (greedy M c).toFinset < weight c I)
    set f' := fun J ↦ weight c J
    have : sT'.Nonempty := by
      use T₁
      grind [M.subset_ground hT₁b.1]
    obtain ⟨T, hT, hT_maxint⟩ := Finset.exists_max_image sT' f' this
    obtain ⟨⟩ := hT
    refine filter_nonempty_iff.mpr ?_
    use T
    grind [M.subset_ground]
-/

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

#check List.getElem_of_mem

open Finset List Encodable in
theorem Matroid_of_greedy {α : Type*} [Encodable α] (F : IndepSystem α)
    (h : ∀ {β : Type}, [LinearOrder β] → [AddCommMonoid β] → [IsOrderedCancelAddMonoid β] →
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
    by_contra! hc
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
    --
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
