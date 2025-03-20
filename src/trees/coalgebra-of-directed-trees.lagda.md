# The coalgebra of directed trees

```agda
open import foundation.function-extensionality-axiom

module
  trees.coalgebra-of-directed-trees
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.bases-directed-trees funext
open import trees.coalgebras-polynomial-endofunctors funext
open import trees.directed-trees funext
open import trees.fibers-directed-trees funext
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
