# Formalization of greedy algorithm on Matroids

## Project description 

The main result of this project is the characterization of finite matroids as independence systems
for which the greedy algorithm gives a max weight base for any cost function. 

The following are included in the project:

- Definition of `IndepSystem` and `FinMatroid` structures for independence systems and finite
matroids respectively. For the latter, the relation to the Mathlib `Matroid` structure is shown,
more details can be found in *FinMatroid/Basic.lean*.
- Definition of `List.select` and `List.selectRel`, which greedily select elements of a list
from right to left (or sorting the list with respect to a relation beforehand). Moreover, useful
theorems for these algorithms, including a characterization when an element is selected:
`List.select_iff`.
- Definition of the "canonical" greedy algorithm for `Greedy.selectRel` repeatedly adding a greatest
element among all element whose selection is allowed by a predicate on the selected elements. For
independence systems this is the `Indep` - the independence oracle. Specializing the relation to
cost gives `FinMatroid.Greedy.greedy`. Equivalence to `List.selectRel` for antisymmetric relations
is also shown, allowing easier proofs.
- `Finmatroid.Matroid_of_greedy` is the proof that an independence system, for which the greedy
algorithm gives a max weight base for any cost function, is a matroid.
- `Finmatroid.greedy_max_weight` is the proof that for any cost function, the greedy algorithm on
a matroid gives a max weight base. 
- `Finmatroid.Matroid_iff_greedy` The biimplication from the previous two results.

## Possible future changes / extensions

- The assumptions on `Finmatroid.Matroid_of_greedy` could be significantly relaxed, requiring only
that the greedy algorithm gives a max weight base for cost functions with a codomain with the
natural numbers as a subset.
- It would be possible to use `Matroid` together with assumptions on the ground set and the
decidability of the `Indep`endence oracle, instead of `FinMatroid` in the theorems.

## References

- D.J.A.Welsh. Matroid Theory. L.M.S Monographs. (London: Academic Press, 1976). ISBN: 012744050X

## AI use

We used ChatGPT as a supplement to LeanSearch, to find theorems. If a specific lemma hadn't been
formalized yet, it sometimes suggested proofs. However, we have not used these, as most of the time
these were incorrect, used Lean3 syntax and / or there were simpler proofs. 

