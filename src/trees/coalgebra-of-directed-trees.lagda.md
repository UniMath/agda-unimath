# The coalgebra of directed trees

```agda
module trees.coalgebra-of-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.bases-directed-trees
open import trees.coalgebras-polynomial-endofunctors
open import trees.directed-trees
open import trees.fibers-directed-trees
open import trees.universal-polynomial-endofunctor
```

</details>

## Idea

Using the [fibers](trees.fibers-directed-trees.md) of
[base elements](trees.bases-directed-trees.md), the type of
[directed trees](trees.directed-trees.md), of which the type of nodes and the
types of edges are of the same [universe level](foundation.universe-levels.md),
has the structure of a [coalgebra](trees.coalgebras-polynomial-endofunctors.md)
for the [polynomial endofunctor](trees.polynomial-endofunctors.md)

```text
  A ↦ Σ (X : Type), (X → A).
```

## Definition

```agda
coalgebra-Directed-Tree :
  (l : Level) →
  coalgebra-polynomial-endofunctor (lsuc l) (universal-polynomial-endofunctor l)
pr1 (coalgebra-Directed-Tree l) = Directed-Tree l l
pr1 (pr2 (coalgebra-Directed-Tree l) T) = base-Directed-Tree T
pr2 (pr2 (coalgebra-Directed-Tree l) T) = fiber-base-Directed-Tree T
```
