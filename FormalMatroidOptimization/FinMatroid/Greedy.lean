import Mathlib.Tactic

import FormalMatroidOptimization.FinMatroid.Basic
import FormalMatroidOptimization.Greedy.Basic
import FormalMatroidOptimization.List.Greedy

namespace FinMatroid

#check Finset.sort

noncomputable def selectRel {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) :
    List α := Greedy.selectRel F.Indep r F.E.toList

noncomputable def selectRel' {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (F : IndepSystem α) :
    List α := List.Greedy.selectRel F.Indep r F.E.toList

end FinMatroid
