import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.Order

/-!
# LinearOrder on a encodable type from a weight function and weights of finite sets

## Main Definitions

* `weight c X` gives the sum of weights `c` of the finite set `X`

* `weightRel c` uses `Order.preimage` to get a transitive and total relation from the weights `c`

* `rel_of_encodable_of_rel r` ensures antisymmetry of the relation `r` using tie-breaking with the
  encoding of the domain.

* `weightRel c'` is `weightRel c` with ties broken. True for elements `a` and `b` if and only if
  `b` has larger weight or the same weight and its position in the encoding is at least that of `a`
-/

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

noncomputable instance {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    (c : α → β) : DecidableRel (weightRel c) := Classical.decRel (weightRel c)
