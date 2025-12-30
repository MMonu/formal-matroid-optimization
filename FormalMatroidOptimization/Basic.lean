import Mathlib.Combinatorics.Matroid.Basic

def IndepSystem.HereditaryProperty {α : Type} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → Y ⊆ X → P Y

structure IndepSystem (α : Type) where
  /-- Independent system has a ground set `E` -/
  (E : Set α)
  /-- Independent system has a predicate `Indep` defining its independent sets -/
  (Indep : Set α → Prop)
  /-- The empty set is `Indep`endent -/
  (indep_empty : Indep ∅)
  /-- For any `Indep`endent set `X`, all its subsets are also `Indep`endent -/
  (indep_mon : IndepSystem.HereditaryProperty Indep)

def Matroid.toIndepSystem {α : Type} (M : Matroid α) : IndepSystem α where
  E := M.E
  Indep := M.Indep
  indep_empty := empty_indep M
  indep_mon := by
    intro X Y hX hY
    exact Indep.subset hX hY
