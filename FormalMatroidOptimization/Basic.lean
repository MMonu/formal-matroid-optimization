import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic

def IndepSystem.HereditaryProperty {α : Type*} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → Y ⊆ X → P Y

structure IndepSystem (α : Type*) where
  /-- Independent system has a ground set `E` -/
  (E : Set α)
  /-- Independent system has a predicate `Indep` defining its independent sets -/
  (Indep : Set α → Prop)
  /-- The empty set is `Indep`endent -/
  (indep_empty : Indep ∅)
  /-- For any `Indep`endent set `X`, all its subsets are also `Indep`endent -/
  (indep_subset : IndepSystem.HereditaryProperty Indep)

def Matroid.toIndepSystem {α : Type*} (M : Matroid α) : IndepSystem α where
  E := M.E
  Indep := M.Indep
  indep_empty := empty_indep M
  indep_subset := by
    intro X Y hX hY
    exact Indep.subset hX hY

#check Finset.induction

open Classical in
noncomputable def GreedySelect {α : Type*} (P : Set α → Prop) (lst : List α) : List α :=
  match lst with
  | []      => []
  | x :: xs =>
    if P (insert x (GreedySelect P xs).toFinset) then
      x :: (GreedySelect P xs)
    else
      GreedySelect P xs

open Classical in
noncomputable def GreedyMin {α : Type*} (F : IndepSystem α) {hF : F.E.Finite} (c : α → ℝ) : List α :=
  have E_lst := (Set.Finite.toFinset hF).toList
  have E_ord := E_lst.mergeSort (fun a b ↦ decide (c a ≤ c b))
  GreedySelect F.Indep E_ord
