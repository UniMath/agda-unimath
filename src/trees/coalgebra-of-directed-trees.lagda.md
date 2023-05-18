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
```

</details>

## Idea

Using the fibers of base elements, the type of directed trees, of which the type
of nodes and the types of edges are of the same universe level, has the
structure of a coalgebra for the polynomial endofunctor

```text
  A ↦ Σ (X : UU), X → A
```

## Definition

```agda
coalgebra-Directed-Tree :
  (l : Level) → coalgebra-polynomial-endofunctor (lsuc l) (UU l) (λ X → X)
pr1 (coalgebra-Directed-Tree l) = Directed-Tree l l
pr1 (pr2 (coalgebra-Directed-Tree l) T) = base-Directed-Tree T
pr2 (pr2 (coalgebra-Directed-Tree l) T) = fiber-base-Directed-Tree T
```
